int f(int i, int * arr) {
  if(i < 0)
    return 0;

  if(i > 10 && arr)
    return arr[i];

  return f(i + 1, arr);
}
