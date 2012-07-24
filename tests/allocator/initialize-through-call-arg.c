#include <stdlib.h>
struct S {
  void* (*allocfn)(size_t);
};

void init2(void* (*f)(size_t), struct S *s) {
  s->allocfn = f;
}

void init(struct S *s) {
  init2(malloc, s);
}


void* derived(struct S* s) {
  return s->allocfn(10);
}
