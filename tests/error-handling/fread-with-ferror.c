#include <stdio.h>

void reportError(void* p) {
}

int target(FILE *stream, int wanted) {
  char buf[10];
  size_t b = fread(buf, 7, wanted, stream);

  // This should fail.  Ideally it wouldn't, but we don't know ahead
  // of time anything about what value ferror should return when fread
  // returns an error.  It could be possible to include this relation
  // in the summary, but it would be very complicated.  For now, this
  // test is expected to not identify any errors here.
  //
  // We would have to rely on other code to tell us either that -22 is
  // an error or reportError is an error reporting function.
  if(b < wanted) {
    if(ferror(stream)) {
      reportError(buf);
      return -22;
    }

  }

  return 0;
}
