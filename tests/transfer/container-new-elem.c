#include <stdlib.h>

struct list_elem_t {
  void *data;
  struct list_elem_t *next;
};

struct list_t {
  struct list_elem_t *head;
};

struct S {
  struct list_t *components;
  struct list_t *properties;
};

struct component {
  double d1;
  float f2;
};

void *list_pop(struct list_t *lst) {
  if(!lst->head)
    return NULL;

  struct list_elem_t *elem = lst->head;
  void *elt = elem->data;
  lst->head = lst->head->next;
  free(elem);
  return elt;
}

struct list_elem_t* list_new_elem(void *d, struct list_elem_t *next) {
  struct list_elem_t *e;
  e = malloc(sizeof(struct list_elem_t));

  e->data = d;
  e->next = next;

  return e;
}

// Instead of allocating the list directly, use a helper function
void list_push(struct list_t *lst, void *comp) {
  struct list_elem_t *e = list_new_elem(comp, lst->head);
  lst->head = e;
}

void add_component(struct S *s, struct component *comp) {
  list_push(s->components, comp);
}

void free_S(struct S *s) {
  void *item;
  while((item = list_pop(s->components)))
    free(item);
  free(s);
}
