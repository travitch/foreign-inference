#include <assert.h>

int* f(int *p1, int *p2) {
  assert(p1);

  return p2;
}
