struct S {
  int *p1;
  int *p2;
};

int *f(struct S *s) {
  return s->p2;
}
