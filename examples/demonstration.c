uint64_t main() {
    uint64_t *x;

    x = malloc(8);

    read(0, x, 8);

    if (*x > 1) {
        if (*x < 6) {
            *x = *x - 2;
            *x = 10 / *x;
        }
    } else
        *x = *x * 2;

    return *x;
}