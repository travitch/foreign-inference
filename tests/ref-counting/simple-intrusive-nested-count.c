#include <stdlib.h>

typedef struct {
  int rc;
} refcount_t;

typedef struct {
  refcount_t ref_count;
} cairo_surface_t;

cairo_surface_t* cairo_surface_create() {
  cairo_surface_t *ret = malloc(sizeof(cairo_surface_t));
  ret->ref_count.rc = 1;

  return ret;
}

cairo_surface_t* cairo_surface_reference(cairo_surface_t *s) {
  ++s->ref_count.rc;

  return s;
}

void cairo_surface_destroy(cairo_surface_t *s) {
  if(--s->ref_count.rc) {
    return;
  }

  free(s);
}
