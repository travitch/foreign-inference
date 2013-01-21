struct S {
  int *p1[100];
  int *p2[5];
};

void f(struct S *s, int *x, int ix) {
  s->p2[ix] = x;
}
