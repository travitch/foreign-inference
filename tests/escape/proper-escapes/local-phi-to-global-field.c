struct S {
  int *x;
  int *y;
};

struct S s;
void addrOfEscape2(int * i1, int * i2, int x) {
  int * p = i2;
  if(x > 10)
    p = i1;

  s.y = p;
}
