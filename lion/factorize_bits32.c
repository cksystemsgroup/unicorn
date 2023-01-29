// cksystemsgroup.github.io/unicorn
// @SOLUTIONS = 2
// @UNROLL_SELFIE = 190
// @UNROLL = 765
// @NAME = factorize (32bit)

// TODO: This is a work-around for missing support of the .rodata section that
// GCC generates for large integers. Inline the value again when we support it.
uint64_t SEMIPRIME = 10967535067;

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
  if (c == SEMIPRIME)
    VERIFIER_error();

  return 0;
}
