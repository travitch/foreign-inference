#include <stdlib.h>

int * allocateInt(int i) {
  int * ret = malloc(sizeof(i));
  *ret = i;

  return ret;
}
