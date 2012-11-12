#include <unistd.h>

void reportError(void *p) {

}

int target(int fd) {
  char buffer[10];
  int bs = read(fd, buffer, 5);
  if(bs < 0) {
    // This conveniently doesn't show up as two error actions because
    // close is an external function (not defined in this module).
    reportError(buffer);
    close(fd);
    return -30;
  }

  return bs + 6;
}

int target2(int fd) {
  close(fd);

  return -5;
}
