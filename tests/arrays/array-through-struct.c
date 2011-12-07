struct S {
  int ** fld;
  double d;
};

extern int x;

int f(int **arr1, double * arr2) {
  struct S s;
  s.fld = arr1;
  s.d = arr2[6];
  return s.fld[3][x] / s.d;
}
