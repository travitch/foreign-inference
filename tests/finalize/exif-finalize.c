#include <stdlib.h>
struct Mem {
  void* (*alloc_func)(size_t);
  void (*free_func)(void*);
};

struct Mem* mem_new(void* (*alloc)(size_t), void (*dealloc)(void*)) {
  struct Mem* m = malloc(sizeof(struct Mem));
  m->alloc_func = alloc;
  m->free_func = dealloc;

  return m;
}

struct Mem* mem_new_default() {
  return mem_new(malloc, free);
}

void exif_mem_free(struct Mem *mem, void *d) {
  mem->free_func(d);
}
