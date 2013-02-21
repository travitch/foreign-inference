#include <unistd.h>

#define EOF 1
#define OK 0
#define FATAL (-1)

int errGen(int fd) {
  char buffer[100];
  int bs;

  bs = read(fd, buffer, 10);
  if(bs < 0)
    return FATAL;

  bs = write(fd, buffer, 1);
  if(bs < 0)
    return EOF;

  return OK;
}

int target(int fd) {
  int rc = errGen(fd);

  if(rc == EOF)
    return FATAL;

  if(rc != OK)
    return rc;

  return 5;
}
