void BZ2_bzWrite(void* b)
{
  int* bzf = (int*)b;

  if (bzf == 0)
    return;


  while (1)
  {
    if (*bzf == 0)
      return;
  }
}
