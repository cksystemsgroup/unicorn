uint64_t main() {
  uint64_t  a;
  uint64_t* x;

  a = 10;
  x = malloc(8);

  *x = 0;

  read(0, x, 1);

  *x = *x - 47;

  a = *x % a;

  if (a == 9)
    return 1;
  else
    return 0;
}
