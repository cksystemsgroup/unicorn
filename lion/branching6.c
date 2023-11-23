// cksystemsgroup.github.io/unicorn
// @SOLUTIONS = 1
// @UNROLL = 100

uint64_t main() {
  uint64_t a;
  uint64_t b;

  a = VERIFIER_nondet_int();
  b = VERIFIER_nondet_int();

  if (a == 0) {
    if (b == 5)
      exit(0);
  }
  a = a - 1;
  exit(0);
}
