int f(int *i, int x) {
  if(x > 10)
    *i = 100;

  return *i + 1;
}
