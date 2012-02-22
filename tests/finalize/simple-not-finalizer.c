#include <stdlib.h>

extern int x;

void f(int * p) {
  if(x)
    free(p);
}
