uint64_t main() {
  uint64_t* x;

  x = malloc(8);

  // address out of range
  x = x + 268435456

  write(1, x, 1);

  return 0;
}
