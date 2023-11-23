// cksystemsgroup.github.io/unicorn
// @SOLUTIONS = 1
// @UNROLL = 100

uint64_t main() {
  uint64_t a;
  uint64_t b;
  uint64_t *x;

  a = 0;

  x = malloc(8);
  *x = 0;

  while (a < 3) {
      b = read(0, x, SIZEOFUINT8);

      if (b == 0) {
          return 0;
      }
      a = a + 1;
  }
  return 0;
}
