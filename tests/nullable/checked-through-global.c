int * p;
int f(int *i) {
  p = i;

  if(p) return *p;

  return 0;
}
