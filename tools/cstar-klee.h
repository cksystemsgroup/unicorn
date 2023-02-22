/*
 * Header file to adapt functions and constants towards KLEE.
 *
 * This header adapts helper functions used throughout the benchmark
 * suite to delegate mostly to KLEE intrinsics. It can be used as a
 * small shim to run benchmarks with KLEE without modifying them.
 */

#include <stdint.h>
#include <stdlib.h>
#include <klee/klee.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>

// Constants for integral byte-sizes.
#define SIZEOFUINT8  sizeof( uint8_t)
#define SIZEOFUINT16 sizeof(uint16_t)
#define SIZEOFINT32  sizeof( int32_t)
#define SIZEOFUINT32 sizeof(uint32_t)
#define SIZEOFUINT64 sizeof(uint64_t)

// Raises a verification error.
#define VERIFIER_error klee_abort

// Asserts a condition holds.
#define VERIFIER_assert klee_assert
void __assert_fail();

uint64_t VERIFIER_nondet_uchar() {
  uint8_t x;
  klee_make_symbolic(&x, sizeof(x), "uint8_t");
  return x;
}

uint64_t *VERIFIER_nondet_p_uchar() {
  uint64_t *x;
  x = malloc(8);
  klee_make_symbolic(x, 8, "uint8_t");
  return x;
}

uint64_t VERIFIER_nondet_ushort() {
  uint16_t x;
  klee_make_symbolic(&x, sizeof(x), "uint16_t");
  return x;
}

uint64_t VERIFIER_nondet_uint() {
  uint32_t x;
  klee_make_symbolic(&x, sizeof(x), "uint32_t");
  return x;
}

uint64_t VERIFIER_nondet_int() {
  int32_t x;
  klee_make_symbolic(&x, sizeof(x), "int32_t");
  return x;
}

#define VERIFIER_two_pow_n(n) (1 << (n))
#define VERIFIER_slt(a, b) ((int64_t)(a) < (int64_t)(b))
