// cksystemsgroup.github.io/unicorn
// @SOLUTIONS = 213
// @UNROLL = 105

uint64_t main() {
  uint64_t* x;

  x = VERIFIER_nondet_uchar();

  *x = *x - 6;

  if (*x > 42)
    // non-zero exit code if the input is > '0' (== 48 == b00110000)
    return 1;
  else if (*x < 42)
    // non-zero exit code if the input is < '0' (== 48 == b00110000)
    return 1;
  else
    return 0;
}
