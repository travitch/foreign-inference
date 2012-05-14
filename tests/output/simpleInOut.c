void f(int x, int * inout) {
  int tmp = *inout;
  *inout = 2 * tmp;
}
