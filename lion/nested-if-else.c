// cksystemsgroup.github.io/unicorn
// @SOLUTIONS = 123
// @UNROLL = 1

uint64_t main() {
  uint64_t  a;
  uint64_t* x;

  a = 40;
  x = VERIFIER_nondet_uchar();

  if (*x > 48) {
    *x = *x - 47;

    if (*x == 2)
      a = a + *x;
    else
      a = a + (*x * 0);
  } else
    a = a + (*x * 0);

  if (a == 42)
    // non-zero exit code if the input is '1' (== 49 == b00110001)
    return 1;
  else
    return 0;
}
