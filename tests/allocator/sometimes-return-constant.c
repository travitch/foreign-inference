#include <stdlib.h>

int zero = 0;

int* f(int x) {
  if(x < 10)
    return &zero;

  return malloc(sizeof(int));
}
