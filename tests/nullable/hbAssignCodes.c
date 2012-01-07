// This test ensures that unrelated conditions do not mask
// non-nullable accesses (here, the length[i] == n condition should
// not prevent code from being recognized as not nullable)
void BZ2_hbAssignCodes(int * code, char * length, int minLen,
    int maxLen, int alphaSize)
{
  int n, vec, i;
  vec = 0;
  for(n = minLen; n <= maxLen; ++n) {
    for(i = 0; i < alphaSize; ++i) {
      if(length[i] == n) {
        code[i] = vec;
        ++vec;
      }
    }
  }
}
