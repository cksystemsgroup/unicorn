/*
  The C* port of simple_3-2.c from github.com/sosy-lab/sv-benchmarks
  for any information about the LICENCE see github.com/sosy-lab/sv-benchmarks

  termination : true
  unreach-call: true
*/

void VERIFIER_error() {
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
  uint64_t  x;
  uint64_t* N;

  N = malloc(8);

  x = 0;
  read(0, N, 8);

  while (x < *N) {
    x = x + 2;
  }

  VERIFIER_assert((x % 2) == 0);
}