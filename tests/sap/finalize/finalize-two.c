#include <stdlib.h>

struct S {
  int *p1;
  int *p2;
  int *p3;
};

void f(struct S *s) {
  free(s->p1);
  free(s->p3);
}
