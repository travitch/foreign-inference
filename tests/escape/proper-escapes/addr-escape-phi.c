extern int ** g;
extern int rand();
void f(int * p) {
  int *x;
  int **y;
  if(rand())
    y = &p;
  else
    y = &x;

  g = y;
}
