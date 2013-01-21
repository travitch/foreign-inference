struct T {
  int *tp1;
  int *tp2;
};

struct S {
  struct T *t1;
  int *p2;
};

int *g(int x, struct T *t) {
  return t->tp2;
}

int *f(struct S *s) {
  return g(55, s->t1);
}
