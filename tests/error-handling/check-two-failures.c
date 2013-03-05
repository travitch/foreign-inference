#include <stdlib.h>

extern int *g1;
extern int *g2;

int target(int sz) {
  void * b1 = malloc(sz);
  void * b2 = malloc(sz);

  if(b1 == NULL || b2 == NULL )
    return -30;

  g1 = b1;
  g2 = b2;

  return 0;
}
