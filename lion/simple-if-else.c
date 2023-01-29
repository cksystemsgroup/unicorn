// cksystemsgroup.github.io/unicorn
// @SOLUTIONS = 1
// @UNROLL_SELFIE = 133
// @UNROLL = 712
// @NAME = simple-if

uint64_t main() {
  uint64_t a;
  uint64_t x;

  a = 40;
  x = VERIFIER_nondet_uchar();

  x = x - 47;

  if (x == 2)
    a = a + x;
  else
    a = a + (x * 0);

  if (a == 42)
    // failure if the input is '1' (== 49 == b00110001)
    VERIFIER_error();
  else
    return 0;
}
