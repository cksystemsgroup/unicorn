// cksystemsgroup.github.io/unicorn
// @SOLUTIONS = 1
// @UNROLL_SELFIE = 100
// @UNROLL = 696
// @NAME = empty (sat)

uint64_t main() {
  uint64_t a;
  uint64_t b;

  a = VERIFIER_nondet_uchar();
  b = 1 / (a - 42);

  return 0;
}
