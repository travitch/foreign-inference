#include <sys/types.h>
#include <fcntl.h>

void FT_Stream_Open(const char *filepathname) {
  open(filepathname, O_RDONLY);
}
