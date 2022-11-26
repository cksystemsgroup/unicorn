// cksystemsgroup.github.io/unicorn
// @SOLUTIONS = 2
// @UNROLL = 191

uint64_t main() {
  uint64_t a;
  uint64_t b;
  uint64_t c;

  a = VERIFIER_nondet_ushort();
  b = VERIFIER_nondet_ushort();

  a = a + 2;
  b = b + 2;

  c = a * b;

  // semi-prime: 7907 * 7919
  if (c == 62615533)
    VERIFIER_error();

  return 0;
}
