#include <stdlib.h>

void outAlloc(int n, int** arr) {
  if(n == 0)
    *arr = NULL;
  else
    *arr = malloc(n * sizeof(int));
}
