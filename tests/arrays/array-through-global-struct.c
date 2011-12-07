struct S {
  int * fld;
  double d;
};

extern int x;
struct S s;

int f(int *arr1, double ** arr2) {
  s.fld = arr1;
  s.d = arr2[6][x];
  return s.fld[x] / s.d;
}
