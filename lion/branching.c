// cksystemsgroup.github.io/unicorn
// @SOLUTIONS = 1
// @UNROLL = 100

uint64_t main() {
  uint64_t a;

  a = VERIFIER_nondet_uchar();

  if (a == 0)
    exit(0);
  else
    while (1) {
      a = a;
    }
}
