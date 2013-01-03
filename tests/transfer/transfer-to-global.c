#include <stdlib.h>

struct S {
  int i;
  int * p;
};

void dispose(struct S *s) {
  free(s->p);
  free(s);
}

struct S s;

void transfer(int * x) {
  s.p = x;
}
