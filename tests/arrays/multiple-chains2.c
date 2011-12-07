extern int x;
extern int * a;
int f(int ** arr) {
  a = arr[5];
  return arr[x][x];
}
