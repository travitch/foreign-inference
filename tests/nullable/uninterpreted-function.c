extern int foo(int *);
void f(int *p) {
  if(foo(p)) *p = 1;
}
