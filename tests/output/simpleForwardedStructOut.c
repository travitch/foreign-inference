struct S {
  int f1;
  double f2;
};

void f(int x, struct S *out) {
  out->f1 = x;
  out->f2 = 1.0 * x / 2.6;
}

void g(int x, struct S *out) {
  f(x, out);
}
