void* (*do_alloc)(int);

int* f(int bytes) {
  return do_alloc(bytes);
}
