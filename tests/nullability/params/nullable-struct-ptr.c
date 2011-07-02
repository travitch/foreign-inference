int g;

struct S {
  int *p;
};

void nullableStructPtr(struct S *s) {
  if(s->p)
    g = *s->p;
}
