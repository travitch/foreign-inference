#include <stdlib.h>

struct S {
  int i;
  int * p;
};

void f(struct S*);

void beLocal(int * x) {
  struct S s;

  if(x)
    s.p = x;
  else
    s.p = malloc(10);

  f(&s);

  if(!x)
    free(s.p);
}
