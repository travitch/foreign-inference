struct S {
  int * sP;
  int * sQ;
};

extern int * g;

void fldEsc(struct S * s) {
  g = s->sP;
}

void proxy(struct S * s) {
  fldEsc(s);
}

void f(int * p) {
  struct S s;
  s.sP = p;
  proxy(&s);
}
