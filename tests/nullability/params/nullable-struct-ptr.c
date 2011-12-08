int g;

struct S {
  int *p;
};

void nullableStructPtr(struct S *s) {
  if(s)
    g = *s->p;
}
