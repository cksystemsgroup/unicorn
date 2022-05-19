// cksystemsgroup.github.io/unicorn
// @SOLUTIONS = 1
// @UNROLL = 83

uint64_t main() {
  uint64_t* x;
  uint64_t a;
  uint64_t b;

  x = malloc(8);
  *x = 0;
  read(0, x, 1);

  a = *x;
  b = 1 / (a - 42);

  return 0;
}
