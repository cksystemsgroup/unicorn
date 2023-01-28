// cksystemsgroup.github.io/unicorn
// @SOLUTIONS = 255
// @UNROLL_SELFIE = 122
// @UNROLL = 703

uint64_t main() {
  uint64_t x;

  x = VERIFIER_nondet_uchar();

  x = x - 6;

  if (x > 42)
    // failure if the input is > '0' (== 48 == b00110000)
    VERIFIER_error();
  else if (x < 42)
    // failure if the input is < '0' (== 48 == b00110000)
    VERIFIER_error();
  else
    return 0;
}
