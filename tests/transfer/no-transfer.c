#include <stdlib.h>

struct S {
  int i;
  int * p1;
  int * p2;
};

void dispose(struct S * s) {
  free(s->p1);
  free(s);
}

void noTransfer(struct S *s, int * x) {
  s->p2 = x;
}
