struct S {
  int *p1;
  int *p2;
};

void f(struct S *s, int *x) {
  s->p2 = x;
}
