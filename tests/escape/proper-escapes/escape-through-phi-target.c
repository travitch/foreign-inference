extern int ** glob;

void f(int * p, int z) {
  int *** t;
  int **x;

  t = &x;
  if(z)
    t = &glob;

  **t = p;
}
