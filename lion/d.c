// cksystemsgroup.github.io/unicorn
// @SOLUTIONS = 255
// @UNROLL = 84

uint64_t* x;
uint64_t main() { 
    uint64_t a;
    // read 1 byte from console into x
    x = VERIFIER_nondet_uchar();

    a = *x;
    a = *(x + a); // segfault if input != 0
}