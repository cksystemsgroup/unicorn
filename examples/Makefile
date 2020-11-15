# Compiler flags
CFLAGS := -Wall -Wextra -c -O0 -g --target=riscv64 -march=rv64gc -D'uint64_t=unsigned long long'

# Cross-Compile *.c into RISC-V *.o executable
%.o: %.c
		clang $(CFLAGS) $< -o $@

# Consider these targets as targets, not files
.PHONY: clean

# Clean up
clean:
		rm -rf *.o
