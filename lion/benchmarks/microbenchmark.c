// cksystemsgroup.github.io/unicorn
// @SOLUTIONS = 1
// @UNROLL = 100

uint64_t main() {
  uint64_t b;
  uint64_t c;
  uint64_t d;
  uint64_t *x;

  d = 0;

  x = malloc(8);
  *x = 0;

  b = read(0, x, 4);
  d = *x;

  c = b;
  while (c > 0) {
    c = c - 1;
  }
  if (d == 1)
    exit(0);

  return 0;
}
