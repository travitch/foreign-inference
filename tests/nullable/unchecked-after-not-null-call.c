#include "base.h"

/*

  Since arr is passed to a call that indicates that it is not
  non-null, we should not count the subsequent unchecked use.
  Essentially, we treat the call as checking arr for nullness.

 */

int f(int * arr, int * arr2) {
  int x = argTwoNotNull(arr, arr2);

  return x + arr[5];
}
