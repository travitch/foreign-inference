#include <stdlib.h>
  /*
   * Format detection is mostly the same as compression
   * detection, with one significant difference: The bidders
   * use the read_ahead calls above to examine the stream rather
   * than having the supervisor hand them a block of data to
   * examine.
   */

struct archive {
  int hdr;
  int hdr2;
};

struct archive_read;

struct archive_format_descriptor {
  void   *data;
  const char *name;
  int (*bid)(struct archive_read *);
  int (*options)(struct archive_read *, const char *key,
      const char *value);
  int (*read_data)(struct archive_read *, const void **, int *, int *);
  int (*read_data_skip)(struct archive_read *);
  int (*cleanup)(struct archive_read *);
};

struct archive_read {
  struct archive  archive;

  struct archive_format_descriptor formats[9];
  struct archive_format_descriptor  *format; /* Active format. */


  int     (*cleanup_archive_extract)(struct archive_read *);
};

int read_data_xz(struct archive_read *a, const void** p, int *o1, int *o2)
{
  return 0;
}

void init_xz(struct archive_read *a)
{
  a->formats[3].read_data = read_data_xz;
}

int read_data_bzip2(struct archive_read *a, const void** p, int *o1, int *o2)
{
  return 0;
}

void init_bzip2(struct archive_read *a)
{
  a->formats[5].read_data = read_data_bzip2;
}

int archive_read_data_block(struct archive *_a,
    const void **buff, int *size, int *offset)
{
  struct archive_read *a = (struct archive_read*)_a;
  if(a->format->read_data == NULL) return -1;

  return (a->format->read_data)(a, buff, size, offset);
}
