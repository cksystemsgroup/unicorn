// cksystemsgroup.github.io/unicorn
// @SOLUTIONS = 1
// @UNROLL = 

uint64_t factorial(uint64_t n) {
  if (n <= 1)
    return n;
  else
    return n * factorial(n - 1);
}

uint64_t main() {
  uint64_t  a;
  uint64_t x;

  x = VERIFIER_nondet_uchar();

  x = x - 39;

  // 3628800 == factorial(10)
  a = factorial(x);

  if (a == 3628800)
    // non-zero exit code if the input is '1' (== 49 == b00110001)
    return 1;
  else
    return 0;
}
