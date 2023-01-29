// cksystemsgroup.github.io/unicorn
// @SOLUTIONS = 1
// @UNROLL_SELFIE = 133
// @UNROLL = 698
// @NAME = div-zero

uint64_t main() {
  uint64_t  a;
  uint64_t x;

  x = VERIFIER_nondet_uchar();

  x = x - 48;

  // division by zero if the input is '0' (== 48 == b00110000)
  a = 41 + (1 / x);

  return 0;
}
