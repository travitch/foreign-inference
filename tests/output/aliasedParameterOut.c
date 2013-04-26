void f(int x, int *out, int *in) {
  if(*in)
    *out = x;
}

void g(int x, int *out) {
  f(x, out, out);
}
