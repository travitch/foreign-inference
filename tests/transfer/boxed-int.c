#include <stdlib.h>

union valueContents {
  int v_enum;
  const char *v_string;
};

struct value {
  int tag;
  double z;
  union valueContents data;
};

struct property {
  double a;
  float x;
  struct value *value;
  struct property *parent;
};

void value_set_method(struct value *val, int v) {
  val->data.v_enum = v;
  val->tag = 0;
}

void value_set_string(struct value *val, const char *s) {
  val->data.v_string = s;
  val->tag = 1;
}

struct value* value_new_method(int v) {
  struct value *val = malloc(sizeof(struct value));
  value_set_method(val, v);
  return val;
}

struct value* value_new_string(const char* s) {
  struct value *val = malloc(sizeof(struct value));
  value_set_string(val, s);
  return val;
}

void property_set_value(struct property *prop, struct value* v) {
  prop->value = v;
}

// This test is problematic because this integer v is stored into a
// union.  One of the union members is finalized (obviously not the
// int), leading to a false-positive Transfer unless the union cases
// are distinguished.
void property_set_method(struct property *prop, int v) {
  property_set_value(prop, value_new_method(v));
}

void property_set_string(struct property *prop, const char *s) {
  property_set_value(prop, value_new_string(s));
}

struct property* property_new_method(int v) {
  struct property *p = malloc(sizeof(struct property));
  property_set_method(p, v);
  return p;
}

struct property* property_new_string(const char *s) {
  struct property *p = malloc(sizeof(struct property));
  property_set_string(p, s);
  return p;
}

void value_free(struct value *v) {
  switch(v->tag) {
  case 1:
    free((void*)v->data.v_string);
    break;
  default:
    break;
  }

  free(v);
}

void property_free(struct property *p) {
  if(!p->parent)
    return;

  value_free(p->value);

  free(p);
}
