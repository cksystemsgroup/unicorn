/*
  The C* port of sum02-2.c from github.com/sosy-lab/sv-benchmarks
  for any information about the LICENCE see github.com/sosy-lab/sv-benchmarks

  termination : true
  unreach-call: true
*/

void VERIFIER_error() {
  uint64_t x;
  x = 10 / 0;
}

uint64_t main() {
  uint64_t  i;
  uint64_t* n;
  uint64_t  sn;
  uint64_t  nl;
  uint64_t  gauss;

  n = malloc(8);
  sn = 0;

  read(0, n, 8);

  i = 0;
  while (i <= *n) {
    sn = sn + i;
    i = i + 1;
  }

  nl = *n;
  gauss = (nl*(nl+1))/2;

  if (sn != gauss) {
    if (sn != 0) {
      VERIFIER_error();
    }
  }

  return 0;
}