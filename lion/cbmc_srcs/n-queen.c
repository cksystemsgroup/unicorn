/*
 * Header file to adapt functions and constants towards CBMC
 */

#include <stdint.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <stdio.h>

// Constants for integral byte-sizes.
#define SIZEOFUINT8  sizeof( uint8_t)
#define SIZEOFUINT16 sizeof(uint16_t)
#define SIZEOFINT32  sizeof( int32_t)
#define SIZEOFUINT32 sizeof(uint32_t)
#define SIZEOFUINT64 sizeof(uint64_t)

// Raises a verification error.
void VERIFIER_error() {
  uint64_t x;
  x = 10 / 0;
}

// Asserts a condition holds, raises verification error otherwise.
void VERIFIER_assert(uint64_t cond) {
  if (cond == 0) {
    VERIFIER_error();
  }
  return;
}

// Returns a zero-extended `unsigned char` (aka. `uint8_t`) value.
uint64_t VERIFIER_nondet_uchar() {
  uint8_t x;
  scanf("%d", &x);
  return x;
}

// Returns a zero-extended pointer to `unsigned char` (aka. `uint8_t`) value.
uint64_t* VERIFIER_nondet_p_uchar() {
  uint64_t *x;
  x = malloc(8);
  *x = VERIFIER_nondet_uchar();
  return x;
}

// Returns a zero-extended `unsigned short` (aka. `uint16_t`) value.
uint64_t VERIFIER_nondet_ushort() {
  uint16_t x;
  scanf("%d", &x);
  return x;
}

// Returns a zero-extended `unsigned int` (aka. `uint32_t`) value.
uint64_t VERIFIER_nondet_uint() {
  uint32_t x;
  scanf("%d", &x);
  return x;
}

// Returns a sign-extended `int` (aka. `int32_t`) value.
uint64_t VERIFIER_nondet_int() {
  int32_t x;
  scanf("%d", &x);
  return x;
}

// Returns `1 << n` (aka. two to the power of n).
uint64_t VERIFIER_two_pow_n(uint64_t n) {
  if (n == 0)
    return 1;
  else if (n < 64)
    return 2 * VERIFIER_two_pow_n(n - 1);
  else
    return 0;
}

// Performs a signed-less-than `a < b` comparison.
uint64_t VERIFIER_slt(uint64_t a, uint64_t b) {
  return a + INT64_MIN < b + INT64_MIN;
}

// cksystemsgroup.github.io/unicorn
// @SOLUTIONS = 1
// @UNROLL = 281

uint64_t main() {
  uint64_t* x;
  uint64_t* y;
  uint64_t  i;
  uint64_t* xi;
  uint64_t* yi;
  uint64_t  j;
  uint64_t* xj;
  uint64_t* yj;
  uint64_t  n;

  n = 1;
  x = malloc(8 * n);
  y = malloc(8 * n);

  i = 0;
  while (i < n) {
    xi = x + i;
    yi = y + i;
    j = 0;

    // Read the x-coordinate of the i-th queen.
    *xi = VERIFIER_nondet_uchar();
    if (*xi >= n) return 0;

    // Read the y-coordinate of the i-th queen.
    *yi = VERIFIER_nondet_uchar();
    if (*yi >= n) return 0;

    // Check for conflict with all previous queens.
    while (j < i) {
      xj = x + j;
      yj = y + j;

      if (*xi == *xj) return 0;              // same column
      if (*yi == *yj) return 0;              // same row
      if (*xi - *xj == *yi - *yj) return 0;  // same main diagonal
      if (*xi - *xj == *yj - *yi) return 0;  // same anti diagonal

      j = j + 1;
    }

    i = i + 1;
  }

  VERIFIER_error();
}
