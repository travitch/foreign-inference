#include <unistd.h>

void reportError(void *p, int i) {

}

int target(int fd, const char *s) {
  char buffer[10];
  int bs = read(fd, buffer, 5);
  if(bs < 0) {
    int l = strlen(s);
    reportError(buffer, l);
    return -30;
  }

  return bs + 6;
}
