#include <stdlib.h>

void* glp_malloc(int size) {
  void* header = malloc(size + 10);
  return (void*)((char*)header + 10);
}
