// cksystemsgroup.github.io/unicorn
// @SOLUTIONS = 1
// @UNROLL = 100

uint64_t main() {
  uint64_t a;
  uint64_t b;
  uint64_t* buffer;

  buffer = malloc(8);
  *buffer = 0;

  read(0, buffer, 1);
  a = *buffer;

  read(0, buffer, 1);
  b = *buffer;

  if (a == 0) {
    if (b == 1)
      exit(0);
  }
  a = a - 1;
  exit(0);
}
