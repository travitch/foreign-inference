/*

  This stub library is used to generate the base.json library
  descriptor for the nullability test suite.

 */

int argOneNotNull(int * arg1, int * arg2);
int argTwoNotNull(int * arg1, int * arg2);
int bothNotNull(int * arg1, int * arg2);
int allArgsNullable(int * arg1, int * arg2);

#if defined(IMPLEMENTATION)

int argOneNotNull(int * arg1, int * arg2) {
  if(arg2) {
    return arg1[5] + arg2[5];
  }

  return 0;
}

int argTwoNotNull(int * arg1, int * arg2) {
  if(!arg1) {
    return arg2[10];
  }

  return arg1[5] + arg2[6];
}

int bothNotNull(int * arg1, int * arg2) {
  return arg1[arg2[5]];
}

int allArgsNullable(int * arg1, int * arg2) {
  if(arg1 && arg2) {
    return arg2[arg1[1]];
  }

  return 0;
}

#endif
