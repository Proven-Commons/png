/*
  The libpng oracle for the header tests in run_tests.py.

  Reads one request per line and prints one answer per line. A
  request is a mode, a space, and the bytes of a PNG file in hex.

    info <hex>   read the file with png_read_info, which reads the
                 signature and every chunk up to the first IDAT,
                 and checks the IHDR fields (png_check_IHDR).
    full <hex>   the same, then decode the image (png_read_image)
                 and read the rest of the file to IEND
                 (png_read_end), so chunks after IDAT are seen too.
    version      print the libpng version this was built against
                 and the one it runs with.

  The answer is `ok:` and the header fields as text, in the shape
  the Lean tool's `header` request uses (`1920x1080 d8 t6 i0`), or
  `none:` and libpng's error message. Warnings do not change the
  answer; the count of them is added as ` warnings:N` when there
  are any.

  libpng's default limits on width and height (one million each)
  are raised to 2^31 - 1, the PNG specification's own cap, so that
  the comparison is with the specification's rule and not with a
  library default. Everything else is libpng's default handling.

  Built by tests/run_tests.py when a C compiler and the libpng
  headers are present; the header oracle section is skipped, and
  says so, when they are not.
*/

#include <png.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

struct source {
  const unsigned char *data;
  size_t len;
  size_t pos;
};

static char error_text[512];
static int warnings;

static void read_bytes(png_structp png, png_bytep out, png_size_t n) {
  struct source *src = (struct source *)png_get_io_ptr(png);
  if (n > src->len - src->pos) {
    png_error(png, "input ends early");
  }
  memcpy(out, src->data + src->pos, n);
  src->pos += n;
}

static void on_error(png_structp png, png_const_charp msg) {
  snprintf(error_text, sizeof error_text, "%s", msg);
  png_longjmp(png, 1);
}

static void on_warning(png_structp png, png_const_charp msg) {
  (void)png;
  (void)msg;
  warnings++;
}

static int hex_value(int c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  if (c >= 'A' && c <= 'F') return c - 'A' + 10;
  return -1;
}

/* Rows of the decoded image; global so the error path can free them. */
static png_bytep *rows;
static png_uint_32 row_count;

static void free_rows(void) {
  if (rows) {
    for (png_uint_32 i = 0; i < row_count; i++) free(rows[i]);
    free(rows);
  }
  rows = NULL;
  row_count = 0;
}

static void answer(int full, const unsigned char *data, size_t len) {
  png_structp png;
  png_infop info;
  struct source src = {data, len, 0};
  png_uint_32 width, height;
  int depth, ctype, interlace;

  error_text[0] = 0;
  warnings = 0;
  png = png_create_read_struct(PNG_LIBPNG_VER_STRING, NULL, on_error, on_warning);
  if (!png) {
    printf("none:could not create a read struct\n");
    return;
  }
  info = png_create_info_struct(png);
  if (!info) {
    png_destroy_read_struct(&png, NULL, NULL);
    printf("none:could not create an info struct\n");
    return;
  }
  if (setjmp(png_jmpbuf(png))) {
    free_rows();
    png_destroy_read_struct(&png, &info, NULL);
    printf("none:%s\n", error_text);
    return;
  }
  png_set_user_limits(png, 0x7fffffffU, 0x7fffffffU);
  png_set_read_fn(png, &src, read_bytes);
  png_read_info(png, info);
  png_get_IHDR(png, info, &width, &height, &depth, &ctype, &interlace, NULL, NULL);
  if (full) {
    png_size_t rowbytes;
    png_set_interlace_handling(png);
    png_read_update_info(png, info);
    rowbytes = png_get_rowbytes(png, info);
    rows = (png_bytep *)calloc(height, sizeof *rows);
    if (!rows) png_error(png, "out of memory");
    row_count = height;
    for (png_uint_32 i = 0; i < height; i++) {
      rows[i] = (png_bytep)malloc(rowbytes ? rowbytes : 1);
      if (!rows[i]) png_error(png, "out of memory");
    }
    png_read_image(png, rows);
    png_read_end(png, NULL);
    free_rows();
  }
  png_destroy_read_struct(&png, &info, NULL);
  printf("ok:%lux%lu d%d t%d i%d", (unsigned long)width, (unsigned long)height, depth,
         ctype, interlace);
  if (warnings) printf(" warnings:%d", warnings);
  printf("\n");
}

int main(void) {
  static char line[1 << 20];
  static unsigned char bytes[1 << 19];
  while (fgets(line, sizeof line, stdin)) {
    size_t n = strlen(line);
    while (n && (line[n - 1] == '\n' || line[n - 1] == '\r')) line[--n] = 0;
    if (strcmp(line, "version") == 0) {
      printf("ok:built %s, running %s\n", PNG_LIBPNG_VER_STRING, png_get_libpng_ver(NULL));
    } else if (strncmp(line, "info ", 5) == 0 || strncmp(line, "full ", 5) == 0) {
      const char *hex = line + 5;
      size_t len = strlen(hex);
      size_t count = 0;
      int bad = (len % 2 != 0) || (len / 2 > sizeof bytes);
      for (size_t i = 0; !bad && i < len; i += 2) {
        int hi = hex_value(hex[i]);
        int lo = hex_value(hex[i + 1]);
        if (hi < 0 || lo < 0) bad = 1;
        else bytes[count++] = (unsigned char)(hi * 16 + lo);
      }
      if (bad) printf("error\n");
      else answer(line[0] == 'f', bytes, count);
    } else {
      printf("error\n");
    }
    fflush(stdout);
  }
  return 0;
}
