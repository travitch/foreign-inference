#include <unistd.h>

void reportError(void *p, int i) {

}

int getlen(const char* s) {
  return s[6];
}

int target(int fd, const char *s) {
  char buffer[10];
  int bs = read(fd, buffer, 5);
  if(bs < 0) {
    int l = getlen(s);
    reportError(buffer, l);
    return -30;
  }

  return bs + 6;
}
