// cksystemsgroup.github.io/unicorn
// @SOLUTIONS = 2
// @UNROLL = 150

uint64_t main() {
  uint64_t* x;
  uint64_t a;
  uint64_t b;
  uint64_t c;

  x = malloc(72);
  *x = 0;
  read(0, x, 1);
  a = *x;

  *(x+1) = 0;
  read(0, x+1, 1);
  b = *(x+1);

  a = a + 2;
  b = b + 2;

  c = a * b;

  // semi-prime: 5 * 7
  if (c == 35)
    return 1;

  return 0;
}
