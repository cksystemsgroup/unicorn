// cksystemsgroup.github.io/unicorn
// @SOLUTIONS = TODO
// @UNROLL = TODO

// 1, 2, 3, 4, 5, 6, 7, 15
// user input value = 42

//#include <stdio.h>

uint64_t main() {
  // size of a single spot (entry) in the reservoir
  uint64_t entry_size;
  // total number of spots (entries) in the reservoir
  uint64_t entry_count;
  // the reservoir itself
  uint64_t* reservoir;
  // loop counters
  uint64_t n;
  uint64_t round;
  uint64_t sum;
  uint64_t avg;
  uint64_t read_bytes;
  // position to replace in reservoir
  uint64_t index;
  // offset for division-by-zero safety property
  // uint64_t offset;
  uint64_t reservoir_at_int_prev;

  // larger numbers require more bits as user input
  // Decimal examples:
  // 42     = 00101010 (1 byte; 6 bits)
  // 4242   = 00010000 10010010 (2 bytes; 13 bits)
  // 424242 = 00000110 01111001 00110010 (3 bytes; 19 bits)
  // 42424242 = 00000010 10000111 01010111 10110010 (4 bytes; 26 bits)
  // offset = 256; 

  entry_size = SIZEOFUINT64; // one spot has 64 bits = 8 bytes
  entry_count = 8; // 8 spots

  // allocate (8 x 8) bytes = 64 bytes
  reservoir = malloc(entry_count * entry_size);

  read_bytes = 0;

  // inital filling of reservoir (dec.):
  //        +--+--+-+--+-+--+--+--+
  //        |38|39|5|24|2|28|18|50|
  //        +--+--+-+--+-+--+--+--+
  // hard-coded, sum = CC (dec: 204)
  *(reservoir + 0) = 38; //0x00000026; // dec: 38
  *(reservoir + 1) = 39; // 0x00000027; // dec: 39
  *(reservoir + 2) = 5; // 0x00000005; // dec: 5
  *(reservoir + 3) = 24; // 0x00000018; // dec: 24
  *(reservoir + 4) = 2; // 0x00000002; // dec: 2
  *(reservoir + 5) = 28; // 0x0000001C; // dec: 28
  *(reservoir + 6) = 18; // 0x00000012; // dec: 18
  *(reservoir + 7) = 50; // 0x00000032; // dec: 50

  // actual reservoir sampling until su
  round = 0;
  sum = 0;
  while (round < 10) {
    // debug
    /*n = 0;
    printf("Reservoir (round %ld): [ ", round);
    while (n < entry_count) {
      printf("%ld ", *(reservoir + n));
      n = n + 1;
    }
    printf("]\n");*/

    // do some work with constant complexity
    // build sum of current reservoir
    n = 0;
    sum = 0;
    while (n < entry_count) {
      sum = sum + *(reservoir + n);
      n = n + 1;
    }
    // compute avg of current reservoir
    avg = sum / entry_count;
    // debug 
    //printf("sum: %ld, avg: %ld\n", sum, avg);


    // replace a "random" element
    index = round % entry_count;
    // debug
    //printf("reservoir[%ld] = %ld", index, *(reservoir + index));

    reservoir_at_int_prev = *(reservoir + index);

    // determine new value by user input
    read_bytes = read(0, (reservoir + index), SIZEOFUINT8);
    //printf(", new bytes = %lx", *(reservoir + index));

    // check if the expected amount of bytes has been read
    if (read_bytes < SIZEOFUINT8) {
    //if (reservoir_at_int_prev == *(reservoir + index)) {
      //*(reservoir + index) = 1 / 0; // (offset - sum);
      //write(0, (reservoir + index), SIZEOFUINT8);
      return 0;
    }

    // debug
    //printf(" ===>>> %ld (read_bytes: %ld)\n", *(reservoir + index), read_bytes);

    round = round + 1;
  }

  return 0;
}
