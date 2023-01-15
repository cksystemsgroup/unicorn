// cksystemsgroup.github.io/unicorn
// @SOLUTIONS = 255
// @UNROLL = 103

uint64_t* x;
uint64_t main() { 
    uint64_t a;
    x = VERIFIER_nondet_p_uchar();
    a = *x;
    a = *(x + a); // segfault if input != 0
    return 0;
}
