// SPDX-License-Identifier: GPL
/*
 * IEI(Inode-bound Execution Integrity)
 * Security Module
 *
 * Author: Zhi Li <lizhi1215@sina.com>
 */

/*
 * ================================================================
 *  设计说明与实现边界
 * ================================================================
 *
 *  本模块用于教学与研究目的，旨在演示一种基于 inode 绑定的
 *  执行完整性机制（Inode-bound Execution Integrity），
 *  重点展示 LSM 钩子、RCU 机制、哈希表组织方式以及
 *  securityfs 接口的实现方法。
 *
 *  为了突出机制本身的结构与并发模型，本实现做了若干
 *  有意识的简化与取舍，说明如下：
 *
 *  1. 文件标识模型
 *     - 文件身份以 (dev, inode) 作为唯一标识。
 *     - 未处理 inode 重用、overlayfs 映射、NFS 语义差异、
 *       bind mount 别名等复杂文件系统行为。
 *     - 未引入文件哈希或 fs-verity 等密码学完整性校验。
 *
 *  2. 策略输入模型
 *     - policy 文件采用简化的文本格式。
 *     - parse_policy_buffer() 假设输入为结构完整的数据块。
 *     - 未实现严格的事务式校验与错误回滚机制。
 *     - 输入格式错误时可能被忽略而非显式报错。
 *
 *  3. 并发模型假设
 *     - clone_policy_rcu() 需在 rcu_read_lock() 保护下调用。
 *     - insert_pair() 假设由调用者保证外部同步。
 *     - policy 写入场景默认单写者模型。
 *
 *  4. 数据结构设计取舍
 *     - training 模式使用链表以便动态插入。
 *     - alerting / enforcing 模式将链表压缩为连续数组，
 *       通过二分查找提升查询效率。
 *     - 为了便于理解结构演进过程，运行期仍保留链表结构，
 *       而未进行进一步内存压缩优化。
 *
 *  5. 监控范围
 *     - 当前仅通过 mmap(PROT_EXEC) 进行执行路径拦截。
 *     - 未覆盖所有可能的可执行映射路径。
 *
 *  本实现强调结构清晰、机制可读与并发模型示例，
 *  不以工业级安全完备性为目标。
 *
 * ================================================================
 */

#include <linux/init.h>
#include <linux/module.h>
#include <linux/kernel.h>
#include <linux/security.h>
#include <linux/fs.h>
#include <linux/mm.h>
#include <linux/mman.h>
#include <linux/slab.h>
#include <linux/hashtable.h>
#include <linux/spinlock.h>
#include <linux/rcupdate.h>
#include <linux/audit.h>
#include <linux/seq_file.h>
#include <linux/uaccess.h>
#include <linux/mutex.h>
#include <linux/lsm_hooks.h>

#define EXE_HASH_BITS 10

enum iei_mode {
  MODE_TRAINING = 0,
  MODE_ALERTING,
  MODE_ENFORCING,
};

static enum iei_mode current_mode = MODE_TRAINING;

struct lib_node {
  /* 为了唯一标识一个文件，需要同时使用 dev 和 inode 号 */
  dev_t dev;
  u64 ino;
  // 挂入 exe_entry 的 libs 链表
  struct hlist_node node;
};

struct exe_entry {
  dev_t exe_dev;
  u64 exe_ino;

  // 挂入 iei_policy 的 buckets 哈希链表
  struct hlist_node node;
  
  // 该可执行文件对应的所有 lib 节点链表头
  struct hlist_head libs;

  // lib_offset 和 lib_count 用于索引
  // iei_policy 实例中的 lib_array中的成员
  u32 lib_count;
  u32 lib_offset;
};

struct iei_policy {
  struct rcu_head rcu;

  // 用于保护插入 exe 和 lib 时的竞争
  struct mutex lock;

  // buckets 是一个哈希表，每个成员是链表头，
  // 指向哈希值相同的所有 exe_entry 实例
  struct hlist_head buckets[1 << EXE_HASH_BITS];

  // 所有 exe 的 lib 节点存储在下面这个数组中
  struct lib_node *lib_array;
  
  // lib_array 中所有成员的总数
  u32 lib_count;
};

// alerting 模式和 enforcing 模式使用的策略
static struct iei_policy __rcu *policy;

// training 模式使用的策略
static struct iei_policy *training_policy;

// 用于更新 policy 指针的自旋锁
static DEFINE_SPINLOCK(update_lock);

// 用于修改 current_mode 和 training_policy 的互斥锁
// 因为 training_policy 与 current_mode 同时变化
// 所以共用一个锁
static DEFINE_MUTEX(mode_lock);

static inline u64 make_key(dev_t dev, u64 ino)
{
  return ((u64)dev << 32) | ino;
}

/* ========================= */
/*
 * 先比较 dev，再比较 inode 号
 */
static int lib_cmp(dev_t d1, u64 i1, dev_t d2, u64 i2)
{
  if (d1 < d2)
    return -1;
  if (d1 > d2)
    return 1;
  if (i1 < i2)
    return -1;
  if (i1 > i2)
    return 1;
  return 0;
}

static struct iei_policy *policy_alloc(void)
{
  struct iei_policy *p;
  int i;

  p = kzalloc(sizeof(*p), GFP_KERNEL);
  if (!p)
    return NULL;

  mutex_init(&p->lock);
  
  for (i = 0; i < (1 << EXE_HASH_BITS); i++)
    INIT_HLIST_HEAD(&p->buckets[i]);

  return p;
}

static void policy_free(struct iei_policy *p)
{
  struct exe_entry *e;
  struct hlist_node *tmp;
  int b;

  // 安全检查
  if (!p) return;
  
  // 第一层循环：遍历哈希桶
  for (b = 0; b < (1 << EXE_HASH_BITS); b++) {
    // 第二层循环：遍历哈希值相同的所有 exe_entry
    hlist_for_each_entry_safe(e, tmp,
			      &p->buckets[b], node) {
      // 第三层循环：遍历属于该 exe_entry 的所有 lib_node
      struct lib_node *ln;
      struct hlist_node *l_tmp;
      hlist_for_each_entry_safe(ln, l_tmp,
				&e->libs, node) {
	hlist_del(&ln->node);
	kfree(ln);
      }

      hlist_del(&e->node);
      kfree(e);
    }
  }

  // 释放 lib_array
  kfree(p->lib_array);

  // 释放 policy 本身
  kfree(p);
}

static void policy_free_rcu(struct rcu_head *rcu)
{
  struct iei_policy *p =
    container_of(rcu, struct iei_policy, rcu);

  policy_free(p);
}

/*
 * 该函数用于向 training 模式转换时，克隆当前正在使用
 * 的策略。函数会深度拷贝 exe_entry 以及其 libs 链表，
 * 但不会拷贝 lib_array。
 * 因为 clone 之后，新的 exe/lib 对会继续插入libs链表，
 * 而在调用 gen_policy_lib_array() 之前，lib_array
 * 不会被使用。
 */
static struct iei_policy *clone_policy_rcu(struct iei_policy *old)
{
  struct exe_entry *e;
  int b;
  struct iei_policy *new;

  // 安全检查
  if (!old) return NULL;
  
  new = policy_alloc();
  if (!new) return NULL;

  /* 深度拷贝 */
  // 第一层循环：遍历哈希桶
  for (b = 0; b < (1 << EXE_HASH_BITS); b++) {
    // 第二层循环：遍历哈希值相同的所有 exe_entry
    struct hlist_node *prev_e = NULL;
    hlist_for_each_entry_rcu(e, &old->buckets[b], node) {
      struct exe_entry *e2;
      e2 = kzalloc(sizeof(*e2), GFP_KERNEL);
      if (!e2)
	goto cleanup;

      e2->exe_dev = e->exe_dev;
      e2->exe_ino = e->exe_ino;
      INIT_HLIST_HEAD(&e2->libs);
      
      if (prev_e == NULL)
	hlist_add_head(&e2->node, &new->buckets[b]);
      else
	hlist_add_behind(&e2->node, prev_e);
      prev_e = &e2->node;

      // 第三层循环：遍历属于该 exe_entry 的所有 lib_node
      struct lib_node *ln;
      struct hlist_node *prev_l=NULL;
      hlist_for_each_entry_rcu(ln, &e->libs, node) {
	struct lib_node *ln2;
	ln2 = kmalloc(sizeof(*ln2), GFP_KERNEL);
	if (!ln2)
	  goto cleanup;

	ln2->dev = ln->dev;
	ln2->ino = ln->ino;
	if (prev_l == NULL)
	  hlist_add_head(&ln2->node, &e2->libs);
	else
	  hlist_add_behind(&ln2->node, prev_l);
	prev_l = &ln2->node;
      }
    }
  }

  return new;

 cleanup:
  policy_free(new);
  return NULL;
}

/*
 * 将所有 exe_entry 的 libs 链表中的 lib 节点复制到
 * policy 的 lib_array 数组之中。
 */
static void gen_policy_lib_array(struct iei_policy *pol)
{
  int b;
  u32 offset;
  struct exe_entry *e;
  struct lib_node *l, *l_arr;

  // policy 的 lib_count 在 insert_pair 中递增
  // 如果为 0，则无需处理
  if (pol->lib_count == 0) return;
  
  /* 分配内存 */
  l_arr = kmalloc_array(pol->lib_count, sizeof(struct lib_node), GFP_KERNEL);
  if (l_arr == NULL) {
    pol->lib_count = 0;
    return;
  }

  /* 填充 lib_array */
  offset = 0;
  // 第一层循环：遍历哈希桶
  for (b=0; b<(1<<EXE_HASH_BITS); b++) {
    // 第二层循环：遍历哈希值相同的所有 exe_entry
    hlist_for_each_entry(e, &pol->buckets[b], node) {
      /* lib_offset 和 lib_count 用于索引
       * iei_policy 实例中的 lib_array
       */
      // exe_entry 初始 lib_count 设为 0
      e->lib_count = 0; 
      // exe_entry 的 lib_offset 为当前数组偏移
      e->lib_offset = offset;
      // 第三层循环：遍历属于该 exe_entry 的所有 lib_node
      hlist_for_each_entry(l, &e->libs, node) {
	l_arr[offset].dev = l->dev;
	l_arr[offset].ino = l->ino;
	// lib_array 偏移加 1
	offset++;
	// exe_entry 的 lib_count 加 1
	e->lib_count++;

	// 安全检查
	if (offset>=pol->lib_count)
	  // 正常情况下，当遍历到最后一个 lib 节点时，
	  // offset 会达到 pol->lib_count，
	  // 三层循环会依次结束。
	  // 如果发生异常导致循环未正确结束，
	  // 会造成越界写入，因此增加此检查。
	  goto out;
      }
    }
  }
 out:
  pol->lib_array = l_arr;
}

/* ========================= */
/* 有序插入                  */
/* ========================= */
/*
 * insert_pair 有两种调用场景：一种是在 training 模式
 * 下，另一种是在写入 policy 文件时。
 */
static void insert_pair(struct iei_policy *p,
			dev_t exe_dev, u64 exe_ino,
			dev_t lib_dev, u64 lib_ino)
{
  struct exe_entry *e;
  u32 bucket;

  // 安全检查，理论上 p 不应为 NULL
  if (!p) return;

  // 计算哈希桶
  bucket = hash_64(make_key(exe_dev, exe_ino),
		   EXE_HASH_BITS);

  // 查找 exe 是否已存在于哈希表中
  bool exe_found = false;
  hlist_for_each_entry(e, &p->buckets[bucket], node) {
    if (e->exe_dev == exe_dev && e->exe_ino == exe_ino) {
      exe_found = true;
      break;
    }
  }
  
  if (!exe_found) {
    // 若不存在，则创建新的 exe_entry
    e = kzalloc(sizeof(*e), GFP_KERNEL);
    if (!e) return;

    e->exe_dev = exe_dev;
    e->exe_ino = exe_ino;
    INIT_HLIST_HEAD(&e->libs);
    hlist_add_head(&e->node, &p->buckets[bucket]);
  }

  /*
   * 查找 lib_node 是否已存在于 exe_entry 的 libs 链表中，
   * 若不存在，则按升序插入。
   */
  struct lib_node *l;
  struct hlist_node *prev = NULL;
  bool lib_found = false;

  hlist_for_each_entry(l, &e->libs, node) {
    int cmp = lib_cmp(lib_dev, lib_ino,
		      l->dev, l->ino);

    if (cmp == 0) {
      lib_found = true;
      break;
    }

    if (cmp < 0) {
      break;
    }

    // prev 指向小于新节点的最大节点
    prev = &l->node;
  }

  if (!lib_found) {
    struct lib_node *new_ln = kmalloc(sizeof(*new_ln),
				      GFP_KERNEL);
    if (new_ln) {
      new_ln->dev = lib_dev;
      new_ln->ino = lib_ino;

      if (!prev)
	hlist_add_head(&new_ln->node,
		       &e->libs);
      else
	hlist_add_behind(&new_ln->node, prev);

      // policy 的 lib_count 递增
      p->lib_count++;
    }
  }
}

// 在 training 模式下插入 exe 和 lib
static void training_insert(dev_t exe_dev, u64 exe_ino,
			    dev_t lib_dev, u64 lib_ino)
{
  mutex_lock(&mode_lock);
  if (training_policy == NULL) {
    mutex_unlock(&mode_lock);
    return;
  }
  mutex_lock(&training_policy->lock);
  insert_pair(training_policy, exe_dev, exe_ino,
	      lib_dev, lib_ino);
  mutex_unlock(&training_policy->lock);
  mutex_unlock(&mode_lock);
}

/* 
 * 在 policy 中查找 exe 和 lib 的配对是否存在 
 */
static bool pair_allowed(dev_t exe_dev, u64 exe_ino,
			 dev_t lib_dev, u64 lib_ino)
{
  struct iei_policy *p;
  struct exe_entry *e, *found_e;
  u32 bucket;
  bool found=false;
  
  rcu_read_lock();

  p = rcu_dereference(policy);
  if (!p)
    goto out;

  bucket = hash_64(make_key(exe_dev, exe_ino),
		   EXE_HASH_BITS);

  // 第一步：查找 exe_entry
  found_e = NULL;
  hlist_for_each_entry_rcu(e, &p->buckets[bucket], node) {
    if (e->exe_dev == exe_dev && e->exe_ino == exe_ino) {
      found_e = e;
      break;
    }
  }

  // 未找到 exe_entry，返回 false
  if (!found_e) goto out;
  
  e = found_e;
  // 防止越界
  if (e->lib_offset + e->lib_count > p->lib_count)
    goto out;

  // 在 policy 的 lib_array 中进行二分查找
  found = false;
  struct lib_node *arr = p->lib_array;
  if (arr==NULL)
    goto out;

  u32 left = 0, right = e->lib_count;
  while (left < right) {
    u32 mid = (left + right) >> 1;
    struct lib_node *ln = &arr[e->lib_offset + mid];

    int cmp = lib_cmp(lib_dev, lib_ino,
		      ln->dev, ln->ino);

    if (cmp == 0) {
      found = true;
      goto out;
    }

    if (cmp < 0)
      right = mid;
    else
      left = mid + 1;
  }
  // 未找到 lib_node，返回 false
 out:
  rcu_read_unlock();
  return found;
}

/* 
 * 审计函数，输出审计消息。
 */
static void iei_audit(dev_t ed, u64 ei,
		      dev_t ld, u64 li,
		      bool blocked)
{
  struct audit_buffer *ab;

  ab = audit_log_start(audit_context(),
		       GFP_KERNEL, AUDIT_KERNEL);

  if (!ab) return;

  audit_log_format(ab,
		   "iei exe_dev=%u exe_ino=%llu lib_dev=%u lib_ino=%llu %s",
		   ed, ei, ld, li,
		   blocked ? "blocked" : "alert");

  audit_log_end(ab);
}

/*
 * mmap 钩子函数
 */
static int iei_mmap_file(struct file *file,
			 unsigned long reqprot,
			 unsigned long prot,
			 unsigned long flags)
{
  struct inode *exe_inode, *lib_inode;
  enum iei_mode mode;

  if (!(prot & PROT_EXEC))
    return 0;

  if (!current->mm || !current->mm->exe_file)
    return 0;

  mode = READ_ONCE(current_mode);
  exe_inode = file_inode(current->mm->exe_file);
  lib_inode = file_inode(file);

  // 安全检查
  if (!exe_inode->i_sb || !lib_inode->i_sb)
    return 0;

  if (mode == MODE_TRAINING) {
    // 在训练模式下记录 exe/lib 对
    training_insert(exe_inode->i_sb->s_dev,
		    exe_inode->i_ino,
		    lib_inode->i_sb->s_dev,
		    lib_inode->i_ino);
    return 0;
  }

  // 在非训练模式下检查是否允许
  if (!pair_allowed(exe_inode->i_sb->s_dev,
		    exe_inode->i_ino,
		    lib_inode->i_sb->s_dev,
		    lib_inode->i_ino)) {

    if (mode == MODE_ALERTING) {
      // 警告模式仅记录审计，不阻止
      iei_audit(exe_inode->i_sb->s_dev,
		exe_inode->i_ino,
		lib_inode->i_sb->s_dev,
		lib_inode->i_ino,
		false);
      return 0;
    } else { // MODE_ENFORCING
      // 强制模式阻止执行并记录审计
      iei_audit(exe_inode->i_sb->s_dev,
		exe_inode->i_ino,
		lib_inode->i_sb->s_dev,
		lib_inode->i_ino,
		true);
      return -EACCES;
    }
  } else {
    // pair 允许执行
    return 0;
  }
}

/* ========================= */
/* LSM hook ID 和注册结构         */
/* ========================= */

static const struct lsm_id iei_id = {
  .name = "iei",
  .id = LSM_ID_IEI,
};

static struct security_hook_list iei_hooks[] __ro_after_init = {
  LSM_HOOK_INIT(mmap_file, iei_mmap_file),
};

/* ========================= */
/* securityfs 文件操作        */
/* ========================= */

/*
 * mode 文件
 */
static ssize_t mode_read(struct file *file,
			 char __user *buf,
			 size_t count,
			 loff_t *ppos)
{
  char tmp[32];
  int len;

  switch (READ_ONCE(current_mode)) {
  case MODE_TRAINING:
    len = scnprintf(tmp, sizeof(tmp), "training\n");
    break;
  case MODE_ALERTING:
    len = scnprintf(tmp, sizeof(tmp), "alerting\n");
    break;
  case MODE_ENFORCING:
    len = scnprintf(tmp, sizeof(tmp), "enforcing\n");
    break;
  default:
    len = scnprintf(tmp, sizeof(tmp), "unknown\n");
  }

  return simple_read_from_buffer(buf, count, ppos, tmp, len);
}

static ssize_t mode_write(struct file *f,
			  const char __user *buf,
			  size_t count, loff_t *ppos)
{
  char kbuf[32];
  enum iei_mode old, new;
  struct iei_policy *old_pol, *new_pol;
  
  if (count >= sizeof(kbuf))
    return -EINVAL;

  if (copy_from_user(kbuf, buf, count))
    return -EFAULT;

  kbuf[count] = 0;

  if (!strncmp(kbuf, "training", 8))
    new = MODE_TRAINING;
  else if (!strncmp(kbuf, "alerting", 8))
    new = MODE_ALERTING;
  else if (!strncmp(kbuf, "enforcing", 9))
    new = MODE_ENFORCING;
  else
    return -EINVAL;

  old = READ_ONCE(current_mode);
  
  if ( old != MODE_TRAINING ) {
    if ( new == MODE_TRAINING ) {
      // 克隆当前 policy 用作训练模式候选
      rcu_read_lock();
      old_pol = rcu_dereference(policy);
      new_pol = clone_policy_rcu(old_pol);
      rcu_read_unlock();

      if (!new_pol)
	return -ENOMEM;

      // 将候选 policy 指针赋给 training_policy
      mutex_lock(&mode_lock);
      if (training_policy)
	policy_free(training_policy);
      
      training_policy = new_pol;
      current_mode = new;
      mutex_unlock(&mode_lock);
      return count;
    }
  } else { // old == MODE_TRAINING
    if (new != MODE_TRAINING) {
      mutex_lock(&mode_lock);

      if (!training_policy) {
	mutex_unlock(&mode_lock);
	return count;
      }
      
      mutex_lock(&training_policy->lock);
      // 生成 lib_array
      gen_policy_lib_array(training_policy);
      mutex_unlock(&training_policy->lock);

      // 更新全局 policy 指针
      spin_lock(&update_lock);
      old_pol = rcu_dereference_protected(policy, lockdep_is_held(&update_lock));
      rcu_assign_pointer(policy, training_policy);
      spin_unlock(&update_lock);

      training_policy = NULL;

      current_mode = new;

      mutex_unlock(&mode_lock);

      if (old_pol)
	call_rcu(&old_pol->rcu, policy_free_rcu);

      return count;
    }
  }

  // 其他情况直接更新 mode
  mutex_lock(&mode_lock);
  current_mode = new;
  mutex_unlock(&mode_lock);
  
  return count;
}

static const struct file_operations mode_fops = {
  .read = mode_read,
  .write = mode_write,
};

/*
 * policy 文件
 */
static int policy_show(struct seq_file *m, void *v)
{
  struct iei_policy *p;
  struct exe_entry *exe;
  struct lib_node *lib;
  int i;
  
  mutex_lock(&mode_lock);
  if (current_mode == MODE_TRAINING) {
    // 得到 training_policy 指针
    p = training_policy;

    // 安全检查
    if (!p) {
      mutex_unlock(&mode_lock);
      return 0;
    }
    
    // 第一层循环：遍历哈希桶
    for (i = 0; i < (1 << EXE_HASH_BITS); i++) {
      // 第二层循环：遍历哈希值相同的所有 exe_entry
      hlist_for_each_entry(exe, &p->buckets[i], node) {
	seq_printf(m, "%u %llu\n", exe->exe_dev, exe->exe_ino);

	// 第三层循环：遍历属于该 exe_entry 的所有 lib_node
	hlist_for_each_entry(lib, &exe->libs, node) {
	  seq_printf(m, "%u %llu\n", lib->dev, lib->ino);
	}
	seq_puts(m, "\n");
      }
    }
    mutex_unlock(&mode_lock);
  } else {
    // 使用 policy 指针, mode_lock 不再需要，释放
    mutex_unlock(&mode_lock);

    rcu_read_lock();

    p = rcu_dereference(policy);
    if (!p) {
      rcu_read_unlock();
      return 0;
    }
    
    // 第一层循环：遍历哈希桶
    for (i = 0; i < (1 << EXE_HASH_BITS); i++) {
      // 第二层循环：遍历哈希值相同的所有 exe_entry
      hlist_for_each_entry_rcu(exe, &p->buckets[i], node) {
	seq_printf(m, "%u %llu\n", exe->exe_dev, exe->exe_ino);

	// 第三层循环：遍历属于该 exe_entry 的所有 lib_node
	// 但是，此处使用 policy 的 lib_array
	u32 idx, b_i, e_i;

	// 赋边界值
	b_i = exe->lib_offset;
	e_i = exe->lib_offset + exe->lib_count;

	// 安全检查，防止溢出
	if (e_i > p->lib_count)
	  e_i = p->lib_count;
	
	for (idx=b_i; idx<e_i; idx++) {
	  lib = p->lib_array + idx;
	  seq_printf(m, "%u %llu\n", lib->dev, lib->ino);
	}
	seq_puts(m, "\n");
      }
    }
    rcu_read_unlock();
  }
  
  return 0;
}

/*
 * 用于读模式打开
 */
static int policy_open_read(struct inode *inode, struct file *file)
{
  if ((file->f_mode & FMODE_WRITE))
    return -EINVAL;

  return single_open(file, policy_show, NULL);
}

/*
 * 用于写模式打开
 */
static int policy_open_write(struct inode *inode, struct file *file)
{
  struct iei_policy *new_policy;

  new_policy = policy_alloc();
  if ( new_policy == NULL ) return -ENOMEM;
  
  file->private_data = new_policy;
  return 0;
}

static int policy_open(struct inode *inode,
		       struct file *file)
{
  bool read  = file->f_mode & FMODE_READ;
  bool write = file->f_mode & FMODE_WRITE;

  if (read && write)
    // 不允许既读又写
    return -EINVAL;

  if (read)
    return policy_open_read(inode, file);

  if (write)
    return policy_open_write(inode, file);

  // 既不读又不写
  return -EINVAL;
}

/*
 * 此函数有待完善，它可以被调用多次，但是每一次的输入必须包含一个
 * 或多个 exe 的全部 lib，否则将出现错误。而这个函数的返回值是
 * void 类型，无法反应错误。
 */
static void parse_policy_buffer(struct iei_policy *pol,
				const char *buf,
				size_t size)
{
#define LINE_MAX 256
  const char *p = buf, *end = buf + size;
  char line[LINE_MAX];
  bool expecting_exe = true;
  size_t len;
  dev_t dev, exe_dev, lib_dev;
  u64 ino, exe_ino, lib_ino;
  int parsed;

  while (p < end) {
    // 获取一行
    len = 0;
    while (p < end && *p != '\n' && len < LINE_MAX - 1)
      line[len++] = *p++;
    line[len] = '\0';

    // 跳过回车
    if (p < end && *p == '\n') p++;

    if (len == 0) {
      // 一个空行意味着一个新的 exe 记录
      expecting_exe = true;
      continue;
    }

    parsed = sscanf(line, "%u %llu", &dev, &ino);
    if (parsed != 2) // 发生了错误
      continue;

    if (expecting_exe) {
      exe_dev = dev;
      exe_ino = ino;
      // 下一行是 lib 的 dev 和 ino
      expecting_exe = false;
    } else {
      lib_dev = dev;
      lib_ino = ino;
      insert_pair(pol, exe_dev, exe_ino, lib_dev, lib_ino);
    }
  }
}

static ssize_t policy_write(struct file *file,
			    const char __user *buf,
			    size_t count,
			    loff_t *ppos)
{
  struct iei_policy *new_policy;
  char *kbuf;

  new_policy = file->private_data;
  if (!new_policy)
    return -EINVAL;
  
  kbuf = kmalloc(count + 1, GFP_KERNEL);
  if (!kbuf)
    return -ENOMEM;

  if (copy_from_user(kbuf, buf, count)) {
    kfree(kbuf);
    return -EFAULT;
  }
  kbuf[count] = '\0';

  parse_policy_buffer(new_policy, kbuf, count);
  kfree(kbuf);

  return count;
}

static int policy_release(struct inode *inode,
			  struct file *file)
{
  enum iei_mode mode;
  
  if (file->f_mode & FMODE_WRITE) {
    struct iei_policy *old_policy;
    struct iei_policy *new_policy = file->private_data;

    if (new_policy) {
      // 获取当前模式
      mode = READ_ONCE(current_mode);

      if (mode == MODE_TRAINING) {
	mutex_lock(&mode_lock);
	if (training_policy)
	  policy_free(training_policy);
	training_policy = new_policy;
	mutex_unlock(&mode_lock);
      } else {
	// 生成 policy 的 lib_array
	gen_policy_lib_array(new_policy);
	
	spin_lock(&update_lock);
	old_policy = rcu_dereference_protected(policy,
		         lockdep_is_held(&update_lock));

	rcu_assign_pointer(policy, new_policy);
	spin_unlock(&update_lock);

	if (old_policy)
	  call_rcu(&old_policy->rcu,
		   policy_free_rcu);
      }
    }
  } else {
    single_release(inode, file);
  }

  return 0;  
}

static const struct file_operations policy_fops = {
  .open    = policy_open,
  .read    = seq_read,
  .write   = policy_write,
  .release = policy_release,
};

/* ========================= */
/* 定义 LSM 并初始化         */
/* ========================= */
static int __init iei_init(void)
{
  struct iei_policy *p;
  struct dentry *iei_dir;

  // 分配 policy
  p = policy_alloc();
  if (!p)
    return -ENOMEM;

  rcu_assign_pointer(policy, p);

  // 注册 LSM hook
  security_add_hooks(iei_hooks,
		     ARRAY_SIZE(iei_hooks),
		     &iei_id);
  
  // 创建 securityfs 目录和文件
  iei_dir = securityfs_create_dir("iei", NULL);
  if (!iei_dir)
    return -EFAULT;
  
  securityfs_create_file("mode",
			 0600,
			 iei_dir,
			 NULL,
			 &mode_fops);

  securityfs_create_file("policy",
			 0600,
			 iei_dir,
			 NULL,
			 &policy_fops);

  pr_info("iei loaded\n");
  return 0;
}

DEFINE_LSM(iei) = {
  .name = "iei",
  .init = iei_init,
};
