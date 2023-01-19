// cksystemsgroup.github.io/unicorn
// @SOLUTIONS = 1
// @UNROLL = 

uint64_t fibonacci(uint64_t n) {
  if (n <= 1)
    return n;
  else
    return fibonacci(n - 1) + fibonacci(n - 2);
}

uint64_t main() {
  uint64_t  a;
  uint64_t x;

  x = VERIFIER_nondet_uchar();

  x = x - 46;

  // 2 == fibonacci(3)
  a = fibonacci(x);

  if (a == 2)
    // non-zero exit code if the input is '1' (== 49 == b00110001)
    return 1;
  else
    return 0;
}
