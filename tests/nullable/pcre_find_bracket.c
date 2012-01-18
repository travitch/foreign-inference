extern int x;
char* pcre_find_bracket(char *code) {
  for(;;) {
    int c = *code;

    if(c == 0) return 0;

    if(c == 100) return code;

    code += x;
  }
}
