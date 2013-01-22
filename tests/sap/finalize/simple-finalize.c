#include <stdlib.h>

struct S {
  int *p1;
  int *p2;
};

void f(int x, struct S *s) {
  free(s->p2);
}
