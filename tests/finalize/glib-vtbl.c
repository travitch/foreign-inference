#include <stdlib.h>

typedef void* gpointer;
typedef size_t gsize;
typedef struct _GMemVTable GMemVTable;

struct _GMemVTable {
  gpointer (*malloc)      (gsize    n_bytes);
  gpointer (*realloc)     (gpointer mem,
      gsize    n_bytes);
  void     (*free)        (gpointer mem);
  /* optional; set to NULL if not used ! */
  gpointer (*calloc)      (gsize    n_blocks,
      gsize    n_block_bytes);
  gpointer (*try_malloc)  (gsize    n_bytes);
  gpointer (*try_realloc) (gpointer mem,
      gsize    n_bytes);
};

static GMemVTable glib_mem_vtable = {
  malloc,
  realloc,
  free,
  calloc,
  malloc,
  realloc,
};

#define G_UNLIKELY(x) x
#define G_LIKELY(x) x

void g_free(gpointer mem) {
  if(G_LIKELY(mem))
    glib_mem_vtable.free(mem);
}
