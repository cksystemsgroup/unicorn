// cksystemsgroup.github.io/unicorn
// @SOLUTIONS = 1
// @UNROLL_SELFIE = 127
// @UNROLL = 920
// @FLAGS = --max-stack 64
// @NAME = invalid-access

uint64_t main() {
  uint64_t a;
  uint64_t* x;

  x = VERIFIER_nondet_p_uchar();

  if (*x == 48)
    // address outside of mapped page -> invalid memory access
    // if the input is '0' (== 48 == b00110000)
    *(x + 32768) = 0;

  a = *x - 7;

  if (a == 42)
    // non-zero exit code if the input is '1' (== 49 == b00110001)
    return 1;
  else
    return 0;
}
