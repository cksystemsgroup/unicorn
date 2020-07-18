/*
The purpose of this code is to demonstrate the capabilities
of the monster model generator of selfie. Monster translates
the code to an SMT-LIB or BTOR2 formula that is satisfiable
if and only if the code exits with a non-zero exit code, or
performs division by zero or invalid/unsafe memory accesses.

Input == #b00110001 (== 49 == '1')
*/

// Pull in the system libc library for what crt0.o likely requires.
use std::process::exit;
use std::io::{stdin, Read};

// Entry point for this program.
#[allow(unconditional_panic)]
#[allow(unused_must_use)]
fn main() {
    let mut x = [0u8];

    stdin().read(&mut x);

    x[0] = x[0] - 48;

    // division by zero if the input was '0' (== 48)
    let mut a = 41 + (1 / x[0]);

    // division by zero if the input was '2' (== 50)
    if x[0] == 2 {
        a = 41 + (1 / 0);
    }

    if a == 42 {
        exit(1);
    } else {
        exit(0);
    }
}

