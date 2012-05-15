void f(int x, int *out) {
  *out = x;
}

void g(int x, int *out) {
  f(x, out);
}
