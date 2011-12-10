int f(int i, int * arr) {
  if(i < 0)
    return 0;

  if(i > 10)
    return arr[i];

  f(i + 1, arr);
}
