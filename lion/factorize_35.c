// cksystemsgroup.github.io/unicorn
// @SOLUTIONS = 2
// @UNROLL_SELFIE = 190
// @UNROLL = 765

uint64_t main() {
  uint64_t a;
  uint64_t b;
  uint64_t c;

  a = VERIFIER_nondet_uchar();
  b = VERIFIER_nondet_uchar();

  a = a + 2;
  b = b + 2;

  c = a * b;

  // semi-prime: 5 * 7
  if (c == 35)
    VERIFIER_error();

  return 0;
}
