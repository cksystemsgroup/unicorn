# Bachelor Theses on Unicorn

## Witness Extraction and Validation in Unicorn by Bernhard Haslauer, University of Salzburg, Austria, 2024 ([PDF](https://github.com/cksystemsgroup/unicorn/blob/main/theses/bachelor_thesis_haslauer.pdf), [Release](https://github.com/cksystemsgroup/unicorn/commit/ebbe6feca5a17438cb82da21712e08517d2b4db4))

Unicorn, a toolchain for symbolic execution, was previously limited to evaluating only whether a given machine code could run into an error state without providing the corresponding inputs for such a case. 
To determine these inputs, a series of steps with external tools have to be run through. 
This Bachelor's thesis explores the possibility of incorporating this feature directly into Unicorn, with the objective of improving Unicorn's capabilities in generating and validating the inputs for these errors states. 
With this proposed extension, Unicorn can extract the inputs and feed them into its built-in RISC-V emulator to validate if these inputs indeed induce the expected errors. 
If the inputs are accurate, the emulator encounters the predicted errors. 
In addition, this thesis provides an insight into the concepts used as well as details about the implementation.


## 32-bit Support for Bit-Precise Modeling of RISC-U Code by Patrick Weber, University of Salzburg, Austria, 2024 ([PDF](https://github.com/cksystemsgroup/unicorn/blob/main/theses/bachelor_thesis_weber.pdf),[Release](https://github.com/cksystemsgroup/unicorn/commit/1d77ed2dac08f1263d4f5f21a3b84a84047cacb8))

This thesis presents the 32-bit support for Unicorn, a symbolic execution engine for bit-precise modeling of RISC-V code. The primary motivation for this development was to improve the engine’s performance and extend its capabilities
to execute 32-bit RISC-U binaries. To this end, we cover the core of the Unicorn engine (on both word and bit level) and discuss the design decisions for implementing the 32-bit support. Our implementation addresses the overflow issues
inherent to addition, subtraction and multiplication in 32-bit systems. The results of our experiment evaluation indicate a significant improvement in the engine’s efficiency and versatility, demonstrating the potential of this approach 
in expanding the applicability of the Unicorn engine. We also discuss the challenges we faced during implementation and show ho we resolved them. This work contributes to the ongoing efforts to optimize symbolic execution engines and 
broadens the scope of their utility in various computing environments. Future work may explore further optimizations and support for other binary types.

# Master's Theses related to Unicorn

## Symbolic Benchmarking for Allocation Efficiency by Jonathan Lainer, University of Salzburg, Austria, 2024 ([PDF](https://github.com/cksystemsgroup/unicorn/blob/main/theses/masters_thesis_lainer.pdf),[Implementation](https://github.com/cksystemsgroup/unicorn/pull/66))

This thesis evaluates the feasability of extending `unicorn`, an SMT based
symbolic execution engine, to count memory and register accesses, thereby
enabling the analysis of memory and register access patterns. As an additional
constraint, the size of the generated SMT formula, and by extention the runtime
of the program, should remain linear in the size of the size of the input
program.

We design and implement an extension to unicorn that facilitates counting
register accesses at first, then extending it to count memory accesses.
Furthermore, we discuss the limitations inherent to the implementation of the
chosen model. We show that the size of the generated SMT formula indeed remains
linear in the size of the input program by providing a formal proof.

Our implementation enables checking for several patterns in binary RISC-V
programs, like finding hot registers and memory locations.
