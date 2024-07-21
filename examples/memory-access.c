// Example in Bernhard Haslauer's Bachelor Thesis.
// invalid memory access if the input was '1' (== 49) or '2' (==50)
uint64_t main() {
    uint64_t  a;
    uint64_t* x;

    x = malloc(8);

    *x = 0;

    read(0, x, 1);

    if (*x == 49)
        // address outside virtual address space -> invalid memory access
        *(x + (4 * 1024 * 1024 * 1024)) = 0;
    if (*x == 50)
        //  address between data and heap -> invalid memory access
        *(x + -2) = 0;

    return 0;
}

