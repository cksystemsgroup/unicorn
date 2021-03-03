uint64_t main() {
  uint64_t  i;
  uint64_t  j;
  uint64_t* x;

  i = 0;
  j = 0;
  x = malloc(8);

  *x = 0;

  read(0, x, 1);

  if (*x < 23) {
    *x = 0;
    while (i < 150) {
      i = i + 1;
    }
    return 1;
  } else {
    *x = 0;
    while (j < 150) {
      j = j + 1;
    }
    return 0;
  }
}
