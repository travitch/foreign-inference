#include <stdlib.h>

void f(char *p) {
  if(p)
    free(p);
}
