// cksystemsgroup.github.io/unicorn
// @SOLUTIONS = 1
// @UNROLL = 100

uint64_t main() {
  uint64_t a;
  uint64_t b;

  a = VERIFIER_nondet_uchar();

  if (a == 0)
    exit(0);
  else {
    b = VERIFIER_nondet_uchar();
    exit(0);
  }
}
