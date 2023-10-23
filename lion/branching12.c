// cksystemsgroup.github.io/unicorn
// @SOLUTIONS = 1
// @UNROLL = 100

uint64_t main() {
  uint64_t a;
  uint64_t b;
  uint64_t c;
  uint64_t *x;

  a = 1;

  x = malloc(8);
  *x = 0;

  while (a <= 3) {
      b = read(0, x, SIZEOFUINT8);

      if (b == 0) {
          return 0;
      }

      b = 0;
      while (b < a * a) {
        c = 0;
        while (c < 20) {
          c = c + 1;
        }

        b = b + 1;
      }

      a = a + 1;
  }
  return 0;
}
