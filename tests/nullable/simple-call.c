extern int x;
int* g(int ** arr) {
  return arr[x];
}

int f(int ** arr) {
  int * a = g(arr);
  return a[3];
}
