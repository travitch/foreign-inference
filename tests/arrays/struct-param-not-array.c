/*
  This test should not have *any* array parameters.  This is to guard
  against accidentally treating struct field references as array
  accesses (they look similar in the IR).
 */
struct S {
  int x;
};

int f(struct S * s) {
  return s->x;
}
