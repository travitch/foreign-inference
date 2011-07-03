struct Pair {
  int *f1;
  int *f2;
};

int g;

void notNullableField(struct Pair *p) {
  if(p->f1)
    g = *p->f2;
}
