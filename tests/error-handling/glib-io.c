#include <stdio.h>
#include <assert.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#include <errno.h>
#include <sys/stat.h>

void g_set_error(int e, void* p) {

}

#define TRUE 1
#define FALSE 0

int learnFrom(int fd) {
  char buffer[100];
  void *p = buffer;
  if(fstat(fd, p) < 0) {
    g_set_error(fd, p);
    return FALSE;
  }

  return TRUE;
}

int get_contents_stdio(FILE *f, int *length, char **contents) {
  size_t total_bytes = 0;

  assert(f != NULL);

  if(!length) {
    g_set_error(total_bytes, length);
    return FALSE;
  }

  return TRUE;
}
