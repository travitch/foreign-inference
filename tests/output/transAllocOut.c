#include <stdlib.h>

void outAlloc(int n, int** arr) {
  *arr = malloc(n * sizeof(int));
}

void outAllocWrapper(int **arr) {
  outAlloc(5, arr);
}
