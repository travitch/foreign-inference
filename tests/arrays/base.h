int oneDimAccess(int * arr, int * in);
int twoDimAccess(int ** arr, int * in);
int threeDimAccess(int *** arr, int * in);
int *oneDimPtrPtr(int ** arr, int i);

#if defined(IMPLEMENTATION)
int oneDimAccess(int * arr, int * in)
{
  return arr[*in];
}

int twoDimAccess(int ** arr, int * in)
{
  return arr[*in][5];
}

int threeDimAccess(int *** arr, int * in)
{
  return arr[1][2][*in];
}

int *oneDimPtrPtr(int ** arr, int i)
{
  return arr[i];
}
#endif
