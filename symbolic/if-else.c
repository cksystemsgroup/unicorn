uint64_t main() {
  uint64_t  a;
  uint64_t* x;

  a = 40;
  x = malloc(8);

  read(0, x, 1);

  if (*x) {
    return 0;
  } else {
    a = a + 40;

    a = a + 60;

    return 1;
  }
}
