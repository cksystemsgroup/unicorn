uint64_t main() {
    uint64_t  a;
    uint64_t* x;

    a = -2147483645;

    x = malloc(8);

    *x = 0;

    read(0, x, 1);

    a = a - *x;

    return a;
}
