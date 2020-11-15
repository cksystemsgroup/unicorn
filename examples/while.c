uint64_t main() {
  uint64_t  i;
  uint64_t* x;

  i = 0;
  x = malloc(8);

  read(0, x, 1);

  while (*x) {
    if (i >= 10)
      return 1;
    else
      i = i + 1;
  }

  return 0;
}
