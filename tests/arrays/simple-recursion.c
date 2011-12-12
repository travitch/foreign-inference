int f(int * arr, int x) {
  if(x == 0)
    return arr[100];

  return f(arr, --x);
}
