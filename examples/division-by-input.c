/*
Example in Bernhard Haslauer's Bachelor Thesis.
Input == #b00110000 (== 48 == '0') or
Input == #b00110010 (== 50 == '2')
 */

uint64_t main() {
    uint64_t  a;
    uint64_t* x;

    x = malloc(8);
    *x = 0;

    read(0, x, 1);

    *x = *x - 48;

    // division by zero if the input was '0' (== 48)
    a = 41 + (1 / *x);

    // division by zero if the input was '2' (== 50)
    if (*x == 2)
        a = 41 + (1 / 0);

    if (a == 42)
        return 1;
    else
        return 0;
}