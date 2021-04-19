uint64_t main() {
  uint64_t  a;
  uint64_t* x;

  x = malloc(8);

  *x = 0;

  read(0, x, 1);

  a = *x - 42;

  if (a < 0)
    return 0;
  if (a > 18446744073709551615)
    return 0;
  if (a == 18446744073709551615)
    return 1;

  return 0;
}
