#define NULL 0

void* pcre_compile2(const char **errorptr, int *errorcodeptr) {

  if(errorptr == NULL) {
    return NULL;
  }

  *errorptr = NULL;
  *errorptr = "foo";

  return errorcodeptr;
}
