// cksystemsgroup.github.io/unicorn
// @SOLUTIONS = TODO
// @UNROLL = TODO

/*#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <unistd.h>*/

uint64_t main() {
  uint64_t* arr;
  uint64_t* buffer;
  uint64_t size;
  uint64_t found_position;

  uint64_t to_swap;

  uint64_t n;
  uint64_t m;

  uint64_t read_bytes;

  size = 8;

  arr = malloc(size * 8);
  buffer = malloc(8);

  *buffer = 0;

  // initialize array with user input
  // printf("Insert initial values.\n");
  n = 0;
  while (n < size) {
    read_bytes = read(0, buffer, 1);

    if (read_bytes == 0)
      size = n;
    else
      *(arr + n) = *buffer;

    n = n + 1;
  }

  // debug
  /*printf("Unsorted array: [ ");
  n = 0;
  while (n < size) {
    printf("%ld ", *(arr + n));
    n = n + 1;
  }
  printf("]\n");
  fflush(stdout);*/

  // sort array using insertion sort
  // worst-case time complexity: O(n^2)
  // best-case time complexity: O(n)
  n = 1;
  while (n < size) {
    // next element to insert into correct slot
    to_swap = *(arr + n);

    // find correct slot
    m = n;
    while (found_position) {
      *(arr + m) = *(arr + m - 1);

      m = m - 1;

      found_position = 0;
      if (m > 0)
        if (*(arr + m - 1) > to_swap)
          found_position = 1;
    }

    // swap next element into correct slot
    *(arr + m) = to_swap;

    n = n + 1;
  }

  // debug
  /*printf("Sorted array: [ ");
  n = 0;
  while (n < size) {
    printf("%ld ", *(arr + n));
    n = n + 1;
  }
  printf("]\n");
  fflush(stdout);

  // gcc / valgrind
  free(arr);*/
}
