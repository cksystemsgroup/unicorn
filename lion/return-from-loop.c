// cksystemsgroup.github.io/unicorn
// @SOLUTIONS = 1
// @UNROLL_SELFIE = 124
// @UNROLL = 718
// @NAME = loop

uint64_t main() {
  uint64_t a;
  uint64_t x;

  x = VERIFIER_nondet_uchar();
  a = 41;

  x = x - 47;
  while (x < 3) {
    a = a + 1;
    x = x + 1;
  }

  if (a == 42)
    // failure if the input is '1' (== 49 == b00110001)
    VERIFIER_error();
  else {
    while (--a > 0); // TODO: This is a work-around to avoid GCC destructors.
    return 0;
  }
}
