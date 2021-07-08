uint64_t main() {
  uint64_t  a;
  uint64_t* x;

  x = malloc(8);

  *x = 0;

  read(0, x, 4);

  a = *x - 48;

  if (a < 9)
    return 0;
  if (a == 9)
    return 1;

  return 0;
}
