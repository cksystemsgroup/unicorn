/*
 * This example stresses capabilities of rarity simulation.
 *
 * To reach a non-zero exit the state that falls into the delay loop
 * needs to be simulated long enough to eventually terminate.
 *
 * Concrete input: [ 49 ] == "1"
 */

uint64_t main() {
  uint64_t  a;
  uint64_t  i;
  uint64_t* x;

  a = 41;
  i = 0;
  x = malloc(8);

  *x = 0;

  read(0, x, 1);

  if (*x == 49) {
    while (i < 1000) {
      i = i + 1;
    }
    a = a + 1;
  }

  if (a == 42)
    return 1;
  else
    return 0;
}
