// cksystemsgroup.github.io/unicorn
// @SOLUTIONS = 1
// @UNROLL = 100

uint64_t main() {
  uint64_t a;

  a = VERIFIER_nondet_uchar();

  if (a == 0)
    exit(0);
  else {
    a = a - 1;
    exit(0);
  }
}
