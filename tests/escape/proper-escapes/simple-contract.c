
typedef void (*funcType)(int *);

extern int g1;
extern int g2;

void libfunc1(int *p)
{
  g1 = *p;
}

void libfunc2(int *p)
{
  g2 = *p;
}

struct S
{
  int * i;
  funcType f;
};


void init1(struct S *s)
{
  s->i = 0;
  s->f = libfunc1;
}

void init2(struct S *s)
{
  s->i = 0;
  s->f = libfunc2;
}

void testF(int * p, int* junk, struct S *globalS)
{
  libfunc1(junk);
  libfunc2(junk);
  init1(globalS);
  init2(globalS);
  globalS->f(p);
}
