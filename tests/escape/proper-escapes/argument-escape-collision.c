extern int* global;

typedef void (*fptr)(int*);

extern fptr indirectCallee;

void g(int *p, int *q)
{
  global = p;
  indirectCallee(q);
}

void f(int *i1, int *i2)
{
  g(i1, i2);
}
