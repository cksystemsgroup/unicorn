uint64_t main() {
  uint64_t  a;
  uint64_t* x;

  a = 40;
  x = malloc(8);

  *x = 0; // touch memory

  read(0, x, 1);

  if (*x > 48) {
    *x = *x - 47;

    if (*x == 2)
      a = a + *x;
    else
      a = a + (*x * 0);
  } else
    a = a + (*x * 0);

  if (a == 42)
    // non-zero exit code if the input is '1' (== 49 == b00110001)
    return 1;
  else
    return 0;
}
