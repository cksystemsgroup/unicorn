// cksystemsgroup.github.io/unicorn
// @SOLUTIONS = 1
// @UNROLL = 190

uint64_t main() {
  uint64_t* x;
  uint64_t* y;
  uint64_t  i;
  uint64_t* xi;
  uint64_t* yi;
  uint64_t  j;
  uint64_t* xj;
  uint64_t* yj;
  uint64_t  n;

  n = 1;
  x = malloc(8 * n);
  y = malloc(8 * n);

  i = 0;
  while (i < n) {
    xi = x + i;
    yi = y + i;
    j = 0;

    // Read the x-coordinate of the i-th queen.
    *xi = 0;  // touch memory
    read(0, xi, 1);
    if (*xi >= n) return 0;

    // Read the y-coordinate of the i-th queen.
    *yi = 0;  // touch memory
    read(0, yi, 1);
    if (*yi >= n) return 0;

    // Check for conflict with all previous queens.
    while (j < i) {
      xj = x + j;
      yj = y + j;

      if (*xi == *xj) return 0;              // same column
      if (*yi == *yj) return 0;              // same row
      if (*xi - *xj == *yi - *yj) return 0;  // same main diagonal
      if (*xi - *xj == *yj - *yi) return 0;  // same anti diagonal

      j = j + 1;
    }

    i = i + 1;
  }

  return 1;
}
