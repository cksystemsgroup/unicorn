// cksystemsgroup.github.io/unicorn
// @SOLUTIONS = 1
// @UNROLL = 100

uint64_t main() {
  uint64_t a;
  uint64_t b;
  uint64_t c;
  uint64_t d;
  uint64_t *x;

  d = 0;

  x = malloc(8);
  *x = 0;

  b = read(0, x, SIZEOFUINT32);
  d = *x;

  c = b;
  while (c > 0) {
    c = c - 1;
  }
  if (d == 1)
    exit(0);

  a = 0;
  while (a < b * b) {
    c = 0;
    while (c < 20) {
      c = c + 1;
    }
    a = a + 1;
  }

  return 0;
}
