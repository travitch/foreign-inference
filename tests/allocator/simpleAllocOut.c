#include <stdlib.h>

void outAlloc(int n, int** arr) {
  *arr = malloc(n * sizeof(int));
}
