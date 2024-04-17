uint64_t main() {
    uint64_t  a;
    uint64_t* x;
    uint64_t y;

    a = 2147483647;

    x = malloc(8);

    *x = 0;

    read(0, x, 1);

    a = a * *x;

    return 0;
}
