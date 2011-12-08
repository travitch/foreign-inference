extern int x;
int f(int *a) {
  if(!a) return 0;

  return a[x];
}
