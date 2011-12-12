#include "base.h"

typedef int (*accessor)(int *, int *);

accessor A = oneDimAccess;

int g(int * arr, int * in) {
  return arr[*in + 5];
}

void setup() {
  A = g;
}

int f(int * arr, int * in) {
  return A(arr, in);
}
