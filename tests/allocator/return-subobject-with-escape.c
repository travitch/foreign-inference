#include <stdlib.h>

typedef struct {
  int userData1;
  int userData2;
} Object;

typedef struct {
  Object o;
  int privateData;
} ObjectWrapper;

void * cache;

Object* allocate(int u1, int u2) {
  ObjectWrapper *ret = malloc(sizeof(ObjectWrapper));
  ret->privateData = 0;
  ret->o.userData1 = u1;
  ret->o.userData2 = u2;

  cache = ret;

  return &ret->o;
}
