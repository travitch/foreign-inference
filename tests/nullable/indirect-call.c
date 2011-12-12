#include "base.h"

typedef int (*NullAccessor)(int*, int*);

NullAccessor A = argOneNotNull;

int neitherNullable(int* a, int* b) {
  return *a + *b;
}


void setup() {
  A = neitherNullable;
}

void f(int * a, int * b) {
  A(a, b);
}
