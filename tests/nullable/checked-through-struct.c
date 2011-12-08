struct S {
  int * ptr;
};

int f(int * arr)
{
  struct S s;
  s.ptr = arr;

  if(s.ptr) return *(s.ptr);

  return 10;
}
