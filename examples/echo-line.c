uint64_t main() {
  uint64_t  a;
  uint64_t* x;

  a = 16;
  x = malloc(8);

  *x = 0;

  while (a) {
    read(0, x, 8);
    write(1, x, 8);
    a = a - 1;
  }

  return *x == 23;
}
