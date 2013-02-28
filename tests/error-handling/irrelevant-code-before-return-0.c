#include <sys/ioctl.h>
#include <errno.h>
#include <stdio.h>
#include <unistd.h>

extern int has_descriptors;

int errorCodesWithZero(int fd) {
  char buf[100];
  int rc = read(fd, buf, 10);
  if(rc < 0)
    return 0;

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
    r = errorCodesWithZero(fd);
    if(r < 0)
      printf("Warning: rc = %d\n", r);
  }

  return 0;
}
