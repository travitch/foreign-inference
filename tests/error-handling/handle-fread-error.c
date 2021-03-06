#include <stdio.h>

void reportError(void* p) {
}

int target(FILE *stream) {
  char buf[10];
  size_t b = fread(buf, 7, 1, stream);
  // This is different from fstat because the return value from read
  // is truncated to 32 bits for the comparison.
  if(b < 1) {
    reportError(buf);
    return -22;
  }

  return b;
}
