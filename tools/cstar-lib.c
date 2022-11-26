/*
 * Library of useful functions and constants for all benchmarks.
 *
 * Note that this library is written in C* (a subset of C) in which the
 * only available integral data type is `uint64_t`. Semantics of other
 * data types are mapped to `uint64_t`, see comments below for details.
 *
 * Note that unless otherwise noted the comments and names used in this
 * library follow the LP64 data model.
 */

// Constants for integral byte-sizes.
uint64_t SIZEOFUINT8 = 1;
uint64_t SIZEOFUINT16 = 2;
uint64_t SIZEOFINT32 = 4;
uint64_t SIZEOFUINT32 = 4;
uint64_t SIZEOFUINT64 = 8;

// Constants for integral limit values.
uint64_t INT32_MIN = 2147483648; // 1 << 31
uint64_t INT64_MIN = 9223372036854775808; // 1 << 63

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
  uint64_t *x;
  x = malloc(8);
  *x = 0;  // touch memory
  read(0, x, SIZEOFUINT8);
  return *x;
}

// Returns a zero-extended `unsigned short` (aka. `uint16_t`) value.
uint64_t VERIFIER_nondet_ushort() {
  uint64_t *x;
  x = malloc(8);
  *x = 0;  // touch memory
  read(0, x, SIZEOFUINT16);
  return *x;
}

// Returns a zero-extended `unsigned int` (aka. `uint32_t`) value.
uint64_t VERIFIER_nondet_uint() {
  uint64_t *x;
  x = malloc(8);
  *x = 0;  // touch memory
  read(0, x, SIZEOFUINT32);
  return *x;
}

// Returns a sign-extended `int` (aka. `int32_t`) value.
uint64_t VERIFIER_nondet_int() {
  uint64_t *x;
  x = malloc(8);
  *x = 0;  // touch memory
  read(0, x, SIZEOFINT32);
  *x = *x - INT32_MIN;
  return *x;
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
