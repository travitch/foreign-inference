struct Pair {
  int *f1;
  int *f2;
};

int g;

void notNullableField(struct Pair *p) {
  g = *p->f2;
}
