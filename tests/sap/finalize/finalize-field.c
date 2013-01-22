#include <stdlib.h>

struct S {
  int *p1;
  int *p2;
};

struct T {
  int x;
  struct S *ps;
};

void g(struct S *s) {
  free(s->p1);
}

void f(struct T *t) {
  g(t->ps);
}
