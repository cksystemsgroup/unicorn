uint64_t main() {
  uint64_t a;
  uint64_t* x;

  a = 7;

  x = malloc(8);

  *x = 0;


  read(0, x, 1);

  *x = *x - a;

  if (*x < 9) {
    return 1;
  } else {
    a = 0;
  }

  return 0;
}
