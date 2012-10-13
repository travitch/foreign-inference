#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>

typedef int(*syscall_ptr)(void);

int openF(const char* fname, int flags, int mode){
  return 0;
}

int closeF(int fd) {
  return 0;
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
  { "fstat", (syscall_ptr)fstat, 0 },
#define sysFstat ((int(*)(int, struct stat*))aSyscall[2].cur)
};

void target(int fd, struct stat* buf) {
  sysFstat(fd, buf);
}
