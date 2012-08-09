// Note, only f:p is shown as escaping in the test output.  the result
// actually has a field of p escaping but there isn't currently a way
// to refer to that, so it looks a bit odd.  As long as f:p escapes,
// though, everything is working.
extern int * glob;

void g(int **p) {
  glob = *p;
}

void f(int * p, int **pp) {
  g(&p);
}
