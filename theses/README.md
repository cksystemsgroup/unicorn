# Bachelor Theses on Unicorn


## 32-bit Support for Bit-Precise Modeling of RISC-U Code by Patrick Weber, University of Salzburg, Austria, 2024 ([PDF](https://github.com/cksystemsgroup/unicorn/blob/main/theses/bachelor_thesis_weber.pdf))

This thesis presents the 32-bit support for Unicorn, a symbolic execution engine for bit-precise modeling of RISC-V code. The primary motivation for this development was to improve the engine’s performance and extend its capabilities
to execute 32-bit RISC-U binaries. To this end, we cover the core of the Unicorn engine (on both word and bit level) and discuss the design decisions for implementing the 32-bit support. Our implementation addresses the overflow issues
inherent to addition, subtraction and multiplication in 32-bit systems. The results of our experiment evaluation indicate a significant improvement in the engine’s efficiency and versatility, demonstrating the potential of this approach 
in expanding the applicability of the Unicorn engine. We also discuss the challenges we faced during implementation and show ho we resolved them. This work contributes to the ongoing efforts to optimize symbolic execution engines and 
broadens the scope of their utility in various computing environments. Future work may explore further optimizations and support for other binary types.
