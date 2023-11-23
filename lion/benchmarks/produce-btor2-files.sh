#!/bin/bash

selfie -c ../../tools/cstar-lib.c tiny-program-good-performance.c -o tiny-program-good-performance.m

selfie -c ../../tools/cstar-lib.c tiny-program-bad-performance.c -o tiny-program-bad-performance.m

selfie -c insertion-sort.c -o insertion-sort.m

selfie -c ../../tools/cstar-lib.c reservoir-sampling.c -o reservoir-sampling.m

selfie -c ../../tools/cstar-lib.c reservoir-sampling-constant-workload.c -o reservoir-sampling-constant-workload.m

time (gtimeout --foreground -v 35m ../../target/release/unicorn beator tiny-program-good-performance.m --unroll 0 --solver z3 --input-limit 2 -t 200000 --one-query -v error --out tiny-program-good-performance-il2.btor2)

time (gtimeout --foreground -v 35m ../../target/release/unicorn beator tiny-program-bad-performance.m --unroll 0 --solver z3 --input-limit 2 -t 200000 --one-query -v error --out tiny-program-good-performance-il2.btor2)

i=0

while [ $i -le 8 ]
do
  echo "microbenchmark z3 input-limit $i"
time (gtimeout --foreground -v 35m ../../target/release/unicorn beator microbenchmark.m --unroll 0 --solver z3 --input-limit $i -t 200000 --one-query -v error --out microbenchmark-il${i}.btor2)
  ((i += 1))
done

time (gtimeout --foreground -v 35m ../../target/release/unicorn beator insertion-sort.m --unroll 0 --solver z3 --input-limit 2 -t 200000 --one-query -v error --out insertion-sort-il${i}.btor2)

i=0

while [ $i -le 8 ]
do
  echo "reservoir-sampling z3 input-limit $i"
time (gtimeout --foreground -v 35m ../../target/release/unicorn beator reservoir-sampling.m --unroll 0 --solver z3 --input-limit $i -t 200000 --one-query -v error --out reservoir-sampling-il${i}.btor2)
  ((i += 1))
done

i=0

while [ $i -le 8 ]
do
  echo "reservoir-sampling-constant-workload z3 input-limit $i"
time (gtimeout --foreground -v 35m ../../target/release/unicorn beator reservoir-sampling-constant-workload.m --unroll 0 --solver z3 --input-limit $i -t 200000 --one-query -v error --out reservoir-sampling-constant-workload-il${i}.btor2)
  ((i += 1))
done
