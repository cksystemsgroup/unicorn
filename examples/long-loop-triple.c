/*
 * This example stresses capabilities of rarity simulation.
 *
 * To reach a non-zero exit the states that consistently fall into the
 * delay loop need to be selected. States that skip the delay loop on
 * any iteration are less interesting.
 *
 * Concrete input: [ 49 50 51 ] == "123"
 */

uint64_t main() {
  uint64_t  a;
  uint64_t  i;
  uint64_t  c;
  uint64_t* x;

  a = 39;
  i = 0;
  c = 0;
  x = malloc(8);

  *x = 0;

  while (c < 3) {
    read(0, x, 1);

    if (*x == (49 + c)) {
      while (i < 100 * c) {
        i = i + 1;
      }
      a = a + 1;
    }

    c = c + 1;
  }

  if (a == 42)
    return 1;
  else
    return 0;
}
