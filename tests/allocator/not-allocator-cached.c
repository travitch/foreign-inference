#include <stdlib.h>

int * last;

int* f(int bytes) {
  last = malloc(bytes);
  return last;
}
