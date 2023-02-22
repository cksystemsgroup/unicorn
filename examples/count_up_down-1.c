/*
  The C* port of count_by_nondet-1.c from github.com/sosy-lab/sv-benchmarks
  for any information about the LICENCE see github.com/sosy-lab/sv-benchmarks

  termination : true
  unreach-call: true
*/

void  VERIFIER_error() {
  uint64_t x;
  x = 10 / 0;
}

void VERIFIER_assert(uint64_t cond) {
  if (cond == 0) {
    VERIFIER_error();
  }
  return;
}

uint64_t main() {
  uint64_t *n;
  uint64_t x;
  uint64_t y;

  n = malloc(8);

  read(0, n, 8); 

  x = *n;
  y = 0;

  while(x > 0) {
    x = x - 1;
    y = y + 1;
  }

  VERIFIER_assert(y == *n);
}
