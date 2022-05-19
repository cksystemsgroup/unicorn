// cksystemsgroup.github.io/unicorn
// @SOLUTIONS = 120
// @UNROLL = 150

uint64_t main() {
  uint64_t* x;
  uint64_t a;
  uint64_t b;
  uint64_t c;

  x = malloc(72);
  *x = 0;
  read(0, x, 4);
  a = *x;

  *(x+1) = 0;
  read(0, x+1, 4);
  b = *(x+1);

  a = a + 2;
  b = b + 2;

  c = a * b;

  // For `n = 10000000000` there are a total of 121 divisors (including
  // 1 and `n` itself), yielding a total of ceil(119 / 2) = 60 distinct
  // pairs of integers whose product is `n`. Taking commutativity into
  // account we get a total of 120 satisfying solutions.
  if (c == 10000000000)
    return 1;

  return 0;
}
