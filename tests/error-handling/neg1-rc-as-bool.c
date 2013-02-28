#include <sys/ioctl.h>
#include <errno.h>

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

  return 0;
}
