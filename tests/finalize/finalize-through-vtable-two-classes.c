#include <stdlib.h>

struct Foo;

struct Vtable {
  void (*close)(struct Foo*);
  void (*finish)(struct Foo*);
  void (*doWrite)(struct Foo*, int, char*);
};

struct Foo {
  struct Vtable *vtbl;
  int * arr;
};

void userFinish(struct Foo* foo) {
  foo->vtbl->finish(foo);
}

void realFinish(struct Foo* foo) {
  free(foo->arr);
  free(foo);
}

void realClose(struct Foo* foo) {
  foo->arr[0] = 0;
}

struct Vtable* readVtable() {
  static struct Vtable vt;
  static int init = 0;

  if(!init) {
    vt.close = realClose;
    vt.finish = realFinish;
  }

  return &vt;
}

void writeClose(struct Foo* foo) {
  foo->arr[0] = 0;
}

void writeFinish(struct Foo* foo) {
  free(foo->arr);
  free(foo);
}

void writeWrite(struct Foo* foo, int nbytes, char * bytes) {
  for(int i = 0; i < nbytes; ++i) {
    foo->arr[i] = bytes[i];
  }
}

struct Vtable* readWriterVtable() {
  static struct Vtable vt;
  static int init = 0;

  if(!init) {
    vt.close = writeClose;
    vt.finish = writeFinish;
    vt.doWrite = writeWrite;
  }

  return &vt;
}

struct Foo* newFoo(int len) {
  struct Foo* foo = calloc(1, sizeof(struct Foo));
  foo->arr = calloc(len, sizeof(int));
  foo->vtbl = readVtable();
  return foo;
}

struct Foo* newFooWriter(int len) {
  struct Foo* foo = calloc(1, sizeof(struct Foo));
  foo->arr = calloc(len, sizeof(int));
  foo->vtbl = readWriterVtable();

  return foo;
}
