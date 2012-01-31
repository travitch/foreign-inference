void f(int n, int m, int * p, int * q) {
  while(n > 0) {
    ++(*p);
  }

  do {
    ++(*q);
  } while (m > 0);
}
