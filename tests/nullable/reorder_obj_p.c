/*
  This test demonstrates an important feature of the LLVM IR: how
  nested field accesses are handled.  The basic IR generated for the
  access below uses two GEP instructions (and the analysis MUST be
  prepared to map them back to %s).

  Right now the analysis passes this test by doing nothing fancy -
  just requiring the -instcombine pass to coalesece the two GEP
  instructions into one.

  This test should guard against regressions here (it comes from
  libacl).
 */

struct A {
  int a;
  int b;
};

struct S {
  int sz;
  struct A a;
};

extern int x;

void acl_reorder_obj_p(struct S *s) {
  x = s->a.b;
}
