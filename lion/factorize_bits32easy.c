// cksystemsgroup.github.io/unicorn
// @SOLUTIONS = 119
// @UNROLL_SELFIE = 190
// @UNROLL = 767
// @NAME = factorize (32bit/easy)

uint64_t main() {
  uint64_t a;
  uint64_t b;
  uint64_t c;

  a = VERIFIER_nondet_uint();
  b = VERIFIER_nondet_uint();

  a = a + 2;
  b = b + 2;

  c = a * b;

  // For `n = 10000000000` there are a total of 121 divisors (including
  // 1 and `n` itself), yielding a total of 119 distinct integers to
  // choose among. Picking `a` from this set also fixes `b` to be one
  // specific value from this set. See the following for details:
  // - https://en.wikipedia.org/wiki/Divisor_function
  if (c == 10000000000)
    VERIFIER_error();

  return 0;
}
