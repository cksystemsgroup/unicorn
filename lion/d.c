// cksystemsgroup.github.io/unicorn
// @SOLUTIONS = 255
// @UNROLL_SELFIE = 103
// @UNROLL = 920
// @NAME = dynamic-memory

uint64_t main() { 
  uint64_t a;
  uint64_t* x;

  x = VERIFIER_nondet_p_uchar();

  a = *x;

  a = *(x + 4096 * a); // segfault if input != 0

  return 0;
}
