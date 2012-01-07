double d[100];
double* bzWriteOpen(int * f, int x, int z) {
  if(!f || x > 10 || z < x) {
    return (double*)0;
  }

  if(z == 100) return 0;

  // Here f is known to be not null, so f is nullable
  return &d[*f];
}
