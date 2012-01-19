#include "base.h"

void f(int * p1, int * p2) {
  int x;
  for(;;) {
    if(argOneNotNull(p1, &x) > 10)
      return;

    p1 = p2;
  }
}
