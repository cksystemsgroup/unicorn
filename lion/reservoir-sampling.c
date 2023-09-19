// cksystemsgroup.github.io/unicorn
// @SOLUTIONS = TODO
// @UNROLL = TODO

// 1, 2, 3, 4, 5, 6, 7, 15
// user input index = 2
// user input value = 42

#include <stdio.h>

uint64_t main() {
  // size of a single spot (entry) in the reservoir
  uint64_t entry_size;
  // total number of spots (entries) in the reservoir
  uint64_t entry_count;
  // the reservoir itself
  uint64_t* reservoir;
  // loop counters
  uint64_t n;
  uint64_t m;
  // number of iterations
  uint64_t sampling_rounds;
  // position to replace in reservoir
  uint64_t index;
  // value to consider for new value in reservoir
  uint64_t new;
  uint64_t old;
  // offset for division-by-zero safety property
  uint64_t offset;

  // TODO: Ask user for number of sampling rounds and offset?
  sampling_rounds = 10;
  // larger numbers require more bits as user input
  // Decimal examples:
  // 42     = 00101010 (1 byte; 6 bits)
  // 4242   = 00010000 10010010 (2 bytes; 13 bits)
  // 424242 = 00000110 01111001 00110010 (3 bytes; 19 bits)
  // 42424242 = 00000010 10000111 01010111 10110010 (4 bytes; 26 bits)
  offset = 42; 

  entry_size = SIZEOFUINT64; // one spot has 64 bits = 8 bytes
  entry_count = SIZEOFUINT64; // 8 spots

  // allocate (8 x 8) bytes = 64 bytes
  reservoir = malloc(entry_count * entry_size);

  // inital filling of reservoir
  n = 0;
  while (n < entry_count) {
    *(reservoir + n) = VERIFIER_nondet_uint();
    n = n + 1;
  }

  // actual reservoir sampling until su
  n = 0;
  while (n < sampling_rounds) {
    // determine index to replace by user input
    index = VERIFIER_nondet_uint();

    // determine new value by user input
    new = VERIFIER_nondet_uint();

    // new value: old value^2 divided by (offset - user input)
    // possibly a division-by-zero if (offset - new) is zero
    if (index >= 0) {
      if (index < entry_count) {
        old = *(reservoir + index);
        new = (old * old) / (offset - new);
      }
    }

    // replace value in reservoir
    if (index >= 0)
      if (index < entry_count)
        *(reservoir + index) = new;

    n = n + 1;
  }

  VERIFIER_error();

  // gcc / valgrind
  // free(reservoir);
}
