// cksystemsgroup.github.io/unicorn
// @SOLUTIONS = 1
// @UNROLL = 105

uint64_t main() {
  uint64_t  a;
  uint64_t* x;

  x = VERIFIER_nondet_uchar();

  a = 0;

  while (a < 10) {

    // non-zero exit code if the input is a digit
    if (*x - 48 == a)
      return 1;

    a = a + 1;
  }

  return 0;
}
