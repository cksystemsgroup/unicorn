// cksystemsgroup.github.io/unicorn
// @SOLUTIONS = 1
// @UNROLL = 100

uint64_t main() {
  uint64_t a;
  uint64_t b;
  uint64_t c;
  uint64_t *x;

  x = malloc(8);
  *x = 0;

  a = 0;
  b = 0;

  c = read(0, x, 2);
  a = *x;

  if (c == 0) {
    exit(0);
  }

  a = a - 1;

  if (a == 1) {
    if (c == 1)
      exit(0);
  }

  a = a - 1;

  if (c == 1) {
    exit(0);
  }

  a = a - 1;

  b = (*x + 1);

  if (b == 1) {
    exit(0);
  }
  if (c == 0) {
    exit(0);
  }

  a = a - 1;
  exit(0);
}