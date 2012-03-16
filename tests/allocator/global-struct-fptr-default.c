#include <stdlib.h>

struct VTbl {
  void* (*vtbl_malloc)(size_t);
  void (*vtbl_free)(void*);
};

struct VTbl vtbl = { malloc, free };

int* allocateIntArray(int n) {
  return vtbl.vtbl_malloc(n * sizeof(int));
}
