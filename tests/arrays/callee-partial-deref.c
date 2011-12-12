#include "base.h"

int f(int ** arr, int x) {
  oneDimPtrPtr(arr, x);
  return arr[x][4];
}
