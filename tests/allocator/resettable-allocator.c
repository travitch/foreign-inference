#include <stdlib.h>

void* (*do_alloc)(size_t) = malloc;

int* f(int bytes) {
  return do_alloc(bytes);
}
