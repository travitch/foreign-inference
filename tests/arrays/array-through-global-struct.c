/*
  I've changed my mind on this test.  Doing a shape analysis to
  note that s.fld aliases arr1 is too expensive.  Do not catch this
  at this point in the analysis.

  This can be changed later and be found by noting that field S.fld is
  used as an array in various points in the application and the
  assignment of arr1 to s.fld makes arr1 an array.
 */
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
