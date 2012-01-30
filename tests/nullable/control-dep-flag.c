void f(int * p) {
  int flag = 0;
  if(p) {
    flag = 1;
  }

  if(flag) *p = 1;
}
