#include <stdlib.h>

void f(int * p, int n) {
  *p = 1;
  exit(-1);
  --n;
}
