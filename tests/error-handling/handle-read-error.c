#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>

void reportError(void* p) {
}

int target(int fd) {
  char buf[10];
  int b = read(fd, buf, 7);
  // This is different from fstat because the return value from read
  // is truncated to 32 bits for the comparison.
  if(b < 0) {
    reportError(buf);
    return -22;
  }

  return b;
}
