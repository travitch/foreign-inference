#include <stdlib.h>
typedef void*(*allocatorType)(size_t);
struct S {
  allocatorType alloc_fn;
  int x;
};

int* f(struct S * s, int n) {
  return s->alloc_fn(n * sizeof(int));
}

extern void* notAllocator(size_t);

void setup(struct S * s) {
  s->alloc_fn = notAllocator;
}
