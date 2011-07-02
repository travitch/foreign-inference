int g;

struct S {
  int *p;
};

void notNullableStructPtr(struct S *s) {
  g = *s->p;
}
