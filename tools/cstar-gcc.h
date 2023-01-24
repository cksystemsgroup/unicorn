#include <stdint.h>
#include <stdlib.h>
#include <unistd.h>

// Constants for integral byte-sizes.
#define SIZEOFUINT8  sizeof( uint8_t)
#define SIZEOFUINT16 sizeof(uint16_t)
#define SIZEOFINT32  sizeof( int32_t)
#define SIZEOFUINT32 sizeof(uint32_t)
#define SIZEOFUINT64 sizeof(uint64_t)

// Raises a verification error.
void VERIFIER_error() {
  exit(1);
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

// Returns a zero-extended pointer to `unsigned char` (aka. `uint8_t`) value.
uint64_t* VERIFIER_nondet_p_uchar() {
  uint64_t *x;
  x = malloc(8);
  *x = 0;  // touch memory
  read(0, x, SIZEOFUINT8);
  return x;
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
