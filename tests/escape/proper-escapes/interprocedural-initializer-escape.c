#include <stdio.h>

struct S {
  int * p;
  int * q;
};

void f(struct S * s, int * i) {
  s->q = i;
}

struct S * global;

void g(int * i) {
  struct S s;
  f(&s, i);

  printf("%d\n", *s.q);

  global = &s;
}
