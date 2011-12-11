#include "base.h"

/*

  Here, arr is passed to a call that checks it for NULL.  This should
  not affect the not-nullability in the caller (f) since it could
  *still* be null.

 */

int f(int * arr, int * arr2) {
  int x = argTwoNotNull(arr, arr2);

  return x + arr[5];
}
