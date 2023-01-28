// cksystemsgroup.github.io/unicorn
// @SOLUTIONS = 1
// @UNROLL_SELFIE = 131
// @UNROLL = 715

uint64_t main() {
  uint64_t a;
  uint64_t x;

  a = 40;
  x = VERIFIER_nondet_uchar();

  if (x <= 48)
    a = a + (x * 0);
  else {
    x = x - 47;

    if (x != 2)
      a = a + (x * 0);
    else
      a = a + x;
  }

  if (a == 42)
    // failure if the input is '1' (== 49 == b00110001)
    VERIFIER_error();
  else
    return 0;
}
