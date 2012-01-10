void f(int (*func)(int)) {
  if(!func) return;

  func(5);
}
