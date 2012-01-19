// if arr2 is ever accessed, it must not be NULL.
int f(int * arr, int * arr2) {
  if(!arr) return 0;

  for(;;) {
    if(arr[5] == 10)
      return 6;

    arr = arr2;
  }
}
