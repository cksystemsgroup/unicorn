// cksystemsgroup.github.io/unicorn
// @SOLUTIONS = 0
// @UNROLL_SELFIE = ?
// @UNROLL = 812
// @NAME = empty (unsat)

uint64_t main() {
  uint64_t a;
  uint64_t b;

  a = VERIFIER_nondet_uchar();
  b = a / 42;

  return 0;
}
