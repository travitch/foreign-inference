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

struct FooRead {
  struct Foo foo;
  int reader;
};

struct FooWrite {
  struct Foo foo;
  int writer;
};

void userFinish(struct Foo* foo) {
  foo->vtbl->finish(foo);
}

void realFinish(struct Foo* foo) {
  struct FooRead* f = (struct FooRead*)foo;
  free(f->foo.arr);
  free(f);
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
  struct FooWrite* f = (struct FooWrite*)foo;
  free(f->foo.arr);
  free(f);
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
  struct FooRead* foo = calloc(1, sizeof(struct FooRead));
  foo->foo.arr = calloc(len, sizeof(int));
  foo->foo.vtbl = readVtable();
  return &foo->foo;
}

struct Foo* newFooWriter(int len) {
  struct FooWrite* foo = calloc(1, sizeof(struct FooWrite));
  foo->foo.arr = calloc(len, sizeof(int));
  foo->foo.vtbl = readWriterVtable();

  return &foo->foo;
}
