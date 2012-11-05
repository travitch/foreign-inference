#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>

void reportError(void* p) {
}

int learnFrom(int fd) {
  struct stat s;
  int b = fstat(fd, &s);
  if(b < 0) {
    reportError(&s);
    return -22;
  }

  return b + 1;
}

int target(int foo) {
  if(foo == 90) {
    reportError(NULL);
    return -50;
  }

  return foo + 12;
}
