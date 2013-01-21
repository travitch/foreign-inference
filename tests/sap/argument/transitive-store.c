struct S {
  int *p1;
  int *p2;
};

struct T {
  int *t1;
  struct S *t2;
};

void g(int *x, struct S *s) {
  s->p1 = x;
}

void f(struct T *t, int *x) {
  g(x, t->t2);
}
