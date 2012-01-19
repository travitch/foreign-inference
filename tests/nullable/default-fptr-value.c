extern void g(int);
void f(int i, void (*fptr)(int)) {
  if(!fptr)
    fptr = g;

  fptr(i);
}
// FIXME: Also need a test for non-fptr vals
// Test function pointers via phi nodes in a loop
