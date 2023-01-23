// cksystemsgroup.github.io/unicorn
// @SOLUTIONS = 2
// @UNROLL = 190

uint64_t main() {
  uint64_t a;
  uint64_t b;
  uint64_t c;

  a = VERIFIER_nondet_uint();
  b = VERIFIER_nondet_uint();

  a = a + 2;
  b = b + 2;

  c = a * b;

  // semi-prime: 104723 * 104729
  if (c == 10967535067)
    VERIFIER_error();

  return 0;
}
