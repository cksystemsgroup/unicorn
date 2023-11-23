// cksystemsgroup.github.io/unicorn
// @SOLUTIONS = 1
// @UNROLL = 100

uint64_t main() {
  uint64_t a;
  uint64_t b;
  uint64_t c;

  a = VERIFIER_nondet_uchar();
  b = VERIFIER_nondet_uchar();
  c = VERIFIER_nondet_uchar();

  if (a == 0) {
    if (b == 1)
      exit(0);
  }
  a = a - 1;
  exit(0);
}
