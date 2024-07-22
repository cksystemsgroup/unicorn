// Example in Bernhard Haslauer's Bachelor Thesis.
// input "11111111" (8 '1's) lead to division by zero
uint64_t main() {
    uint64_t a;
    uint64_t* x;

    x = malloc(8);
    *x = 0;

    read(0, x, 8);

    a = 3544668469065756977;
    // input == "11111111" ==  3544668469065756977
    if (*x == a)
        *x = 42 / 0;

    return 0;
}

