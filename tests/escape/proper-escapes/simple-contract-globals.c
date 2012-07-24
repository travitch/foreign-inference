
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

struct S *globalS;

void init1()
{
  globalS->i = 0;
  globalS->f = libfunc1;
}

void init2()
{
  globalS->i = 0;
  globalS->f = libfunc2;
}

void testF(int * p, int* junk)
{
  libfunc1(junk);
  libfunc2(junk);
  init1();
  init2();
  globalS->f(p);
}
