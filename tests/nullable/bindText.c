#include "base.h"
#include <string.h>

extern char *str;

int bindText(int* zData, void (*xDel)(void*)) {
  int rc = strlen(str);
  if(rc == 0) {
    if(zData != 0) {
      rc = argOneNotNull(&rc, zData);
      if(rc != 5) {
        rc = 5;
      }
    }
  }
  else if(xDel != 0 && xDel != (void*)-1) {
    xDel((void*)zData);
  }

  return rc;
}
