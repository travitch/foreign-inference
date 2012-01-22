#include "base.h"

extern int * g;
void f(int * p) {
  if(!p)
    p = g;

  argOneNotNull(p, g);
}
