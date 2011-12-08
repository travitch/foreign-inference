struct S {
  int data;
};

extern int x;
int f(struct S * s) {
  if(!s) return 0;

  return s->data;
}
