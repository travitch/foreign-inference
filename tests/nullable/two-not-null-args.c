int f(int * arr1, int * arr2, int * arr3) {
  if(arr3) {
    return arr3[5];
  }

  return arr1[arr2[5]];
}
