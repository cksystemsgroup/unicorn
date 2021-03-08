uint64_t main() {
  uint64_t* x;

  x = malloc(16);

  *x = 0;

  // accesses uninitialized memory
  write(1, x, 12);

  return 0;
}
