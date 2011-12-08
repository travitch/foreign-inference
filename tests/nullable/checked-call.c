extern int x;
int* g(int ** arr) {
  if(arr)
    return arr[x];
  return &x;
}

int f(int ** arr) {
  int * a = g(arr);
  return a[3];
}
