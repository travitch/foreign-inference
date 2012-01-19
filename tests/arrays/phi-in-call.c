#include "base.h"
void f(int * arr, int * arr2, int * p) {
  for(;;) {
    oneDimAccess(arr, p);
    arr = arr2;
  }
}
