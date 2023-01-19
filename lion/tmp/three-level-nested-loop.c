// cksystemsgroup.github.io/unicorn
// @SOLUTIONS = 1
// @UNROLL = 

uint64_t main() {
  uint64_t  a;
  uint64_t x;

  a = 0;
  x = VERIFIER_nondet_uchar();

  x = x - 49;

  while (x < 15) {
    while (x < 10) {
      while (x < 5) {
        a = a + 1;
        x = x + 1;
      }

      a = a + 1;
      x = x + 1;
    }

    a = a + 1;
    x = x + 1;
  }

  a = a + 27;

  if (a == 42)
    // non-zero exit code if the input is '1' (== 49 == b00110001)
    return 1;
  else
    return 0;
}
