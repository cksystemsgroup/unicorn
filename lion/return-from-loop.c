// cksystemsgroup.github.io/unicorn
// @SOLUTIONS = 10
// @UNROLL_SELFIE = 124
// @UNROLL = 807
// @NAME = loop

uint64_t main() {
  uint64_t a;
  uint64_t x;
  uint64_t f;

  x = VERIFIER_nondet_uchar();
  f = 0;
  a = 0;

  while (a < 10) {

    // failure if the input is a digit
    if (x - 48 == a)
      f = 1;

    a = a + 1;
  }

  if (f > 0)
    VERIFIER_error();

  return 0;
}
