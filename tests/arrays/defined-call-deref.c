extern int v;
void g(int * arr, int * x) {
  v = arr[*x];
}

int f(int * arr, int x) {
  g(arr, &x);
  return x;
}
