#include <stdlib.h>

int * g;

void outAlloc(int n, int** arr) {
  // This is not an alloc-out parameter because the result escapes
  // via a different assignment.
  int * mem = malloc(n * sizeof(int));
  *arr = mem;
  g = mem;
}
