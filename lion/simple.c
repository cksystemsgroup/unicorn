// cksystemsgroup.github.io/unicorn
// @SOLUTIONS = 1
// @UNROLL = 100

uint64_t main() {
  uint64_t a;
  uint64_t b;

  a = VERIFIER_nondet_uchar();
  b = 1 / (a - 42);

  return 0;
}
