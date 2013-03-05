#include <stdlib.h>
#include <unistd.h>

extern int *g1;
extern int *g2;

int target(int fd) {
  char buffer[100];
  int rc1 = read(fd, buffer, 1);
  int rc2 = read(fd, buffer, 2);

  if(rc1 == -1 || rc2 == -1)
    return -30;

  *g1 = rc1;
  *g2 = rc2;

  return 0;
}
