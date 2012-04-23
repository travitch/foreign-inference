#include <stdlib.h>

typedef struct {
  int ref_count;
} cairo_surface_t;

cairo_surface_t* cairo_surface_create() {
  cairo_surface_t *ret = malloc(sizeof(cairo_surface_t));
  ret->ref_count = 1;

  return ret;
}

cairo_surface_t* cairo_surface_reference(cairo_surface_t *s) {
  ++s->ref_count;

  return s;
}

void cairo_surface_destroy(cairo_surface_t *s) {
  if(--s->ref_count) {
    return;
  }

  free(s);
}
