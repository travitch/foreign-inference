#include <stdlib.h>

struct S {
  int *p1;
  int *p2;
};

void g(struct S *s) {
  free(s->p2);
}

void f(struct S *s) {
  g(s);
}
