#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>

void reportError(void* p) {
}

int learnFrom(int fd) {
  struct stat s;
  int b = fstat(fd, &s);

  return b;
}

int target(int fd) {
  if(learnFrom(fd) < 0) {
    reportError(NULL);
    return -2;
  }

  return 8;
}
