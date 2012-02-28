#include <stdlib.h>

int * arr(int nelems) {
  if(nelems <= 0)
    return NULL;

  return malloc(nelems * sizeof(int));
}
