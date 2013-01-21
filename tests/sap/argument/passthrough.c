struct S {
  int *p1;
  int *p2;
};

void g(int *x, struct S* s) {
  s->p2 = x;
}

void f(int *x, struct S *s) {
  g(x, s);
}
