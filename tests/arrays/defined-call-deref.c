void g(int * arr, int * x) {
  (void)arr[*x];
}

int f(int * arr, int x) {
  g(arr, &x);
  return x;
}
