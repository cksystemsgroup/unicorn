// cksystemsgroup.github.io/unicorn
// @SOLUTIONS = 1
// @UNROLL = 100

uint64_t main() {
  uint64_t a;
  uint64_t b;
  uint64_t* buffer;

  *buffer = 0;

  read(0, buffer, 1);
  a = *buffer;

  if (a == 0)
    exit(0);
  else {
    read(0, buffer, 1);
    b = *buffer;
    exit(0);
  }
}
