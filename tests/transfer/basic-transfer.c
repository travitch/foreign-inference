#include <stdlib.h>

struct S {
  int i;
  int * p;
};

void dispose(struct S *s) {
  free(s->p);
  free(s);
}

void transfer(int * x, struct S *s) {
  s->p = x;
}
