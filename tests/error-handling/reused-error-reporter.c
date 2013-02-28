#include <sys/ioctl.h>
#include <errno.h>
#include <stdio.h>
#include <unistd.h>

extern int has_descriptors;

void reportError(int fd) {

}

int errorCodeGen(int fd) {
  char buf[100];
  int rc = read(fd, buf, 10);
  if(rc < 0) {
    reportError(fd);
    return -100;
  }

  return fd + 5;
}

int ioctlWrapper(int fd, int ionum) {
  char buffer[100];
  int r = ioctl(fd, ionum, buffer);
  if(r) {
    if(errno == EINVAL)
      return -100;
    else if(errno == EBUSY)
      return -20;
    else if(errno == ENODEV)
      return -5;

    return -99;
  }

  // This should have no effect on the results.  It turns out that it
  // doesn't - instead the problem in libusb (op_set_configuration)
  if(!has_descriptors) {
    r = errorCodeGen(fd);
    if(r < 0)
      reportError(r);
//      printf("Warning: rc = %d\n", r);
  }

  return 0;
}
