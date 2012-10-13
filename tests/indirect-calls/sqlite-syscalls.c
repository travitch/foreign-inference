typedef int(*syscall_ptr)(void);

int openF(const char* fname, int flags, int mode){
  return 0;
}

int closeF(int fd) {
  return 0;
}

int accessF(const char *pathname, int mode) {
  return 1;
}

struct unix_syscall {
  const char *name;
  syscall_ptr cur;
  syscall_ptr def;
} aSyscall[] = {
  { "open", (syscall_ptr)openF, 0 },
#define sysOpen ((int(*)(const char*, int, int))aSyscall[0].cur)
  { "close", (syscall_ptr)closeF, 0 },
#define sysClose ((int(*)(int))aSyscall[1].cur)
  { "access", (syscall_ptr)accessF, 0 },
#define sysAccess ((int(*)(const char*, int))aSyscall[2].cur)
};

void target(int fd) {
  sysClose(fd);
}
