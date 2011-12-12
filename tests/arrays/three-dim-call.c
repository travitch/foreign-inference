#include "base.h"

void f(int *** arr) {
  int x;
  threeDimAccess(arr, &x);
}
