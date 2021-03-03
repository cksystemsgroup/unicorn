/*
 * This example stresses capabilities of rarity simulation.
 *
 * To reach a non-zero exit the state that overcomes the delay loop
 * needs to be duplicated often enough to hit the bug.
 *
 * Concrete input: [ 49 ] == "1"
 */

uint64_t main() {
  uint64_t  i;
  uint64_t* x;

  i = 0;
  x = malloc(8);

  *x = 0;

  while (i < 150) {
    i = i + 1;
  }

  read(0, x, 1);

  if (*x == 49)
    return 1;
  else
    return 0;
}
