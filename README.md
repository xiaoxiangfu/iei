IEI(Inode-bound Execution Integrity) LSM. It is created for a chapter of a new book 《Linux内核安全实战》.

Usages:

1. in Linux kernel source tree (>=6.8), under security, create directory "iei".
2. copy this project's files Kconfig, Makefile, and iei.c into the directory "iei".
3. modify security/Kconfig, add one line: source "security/iei/Kconfig". Please reference "Kconfig.diff".
4. modify include/uapi/linux/lsm.h, add one line: #define LSM_ID_IEI 112. Please reference "lsm.h.diff".
5. make kernel
