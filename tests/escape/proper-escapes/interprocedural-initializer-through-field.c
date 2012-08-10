#include <stdio.h>

struct S {
  int * p;
  int * q;
};

void f(int ** s, int * i) {
  *s = i;
}

void g(int * i) {
  struct S s;
  f(&s.q, i);

  printf("%d\n", *s.q);
}
