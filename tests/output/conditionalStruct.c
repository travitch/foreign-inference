struct S {
  int f1;
  double f2;
};

extern struct S glob;

void f(struct S *out) {
  if(out) {
    *out = glob;
  }
}
