#!/bin/bash

: '
echo "branching3 n=180 boolector input-limit 1"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching3.m --unroll 180 -p --solver boolector --find-bounds --input-limit 1)
echo "branching3 n=180 boolector input-limit 1 less-input"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching3.m --unroll 180 -p --solver boolector --find-bounds --input-limit 1 --less-input)

echo "branching3 n=180 z3 input-limit 1"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching3.m --unroll 180 -p --solver z3 --find-bounds --input-limit 1 -t 200000)
echo "branching3 n=180 z3 input-limit 1 less-input"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching3.m --unroll 180 -p --solver z3 --find-bounds --input-limit 1 --less-input -t 200000)

echo "branching3 n=256 boolector input-limit 1"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching3.m --unroll 256 -p --solver boolector --find-bounds --input-limit 1 -t 200000)
echo "branching3 n=256 boolector input-limit 1 less-input"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching3.m --unroll 256 -p --solver boolector --find-bounds --input-limit 1 --less-input -t 200000)

echo "branching3 n=256 z3 input-limit 1"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching3.m --unroll 256 -p --solver z3 --find-bounds --input-limit 1)
echo "branching3 n=256 z3 input-limit 1 less-input"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching3.m --unroll 256 -p --solver z3 --find-bounds --input-limit 1 --less-input)

echo "branching4 n=256 boolector input-limit 2"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching4.m --unroll 256 -p --solver boolector --find-bounds --input-limit 2 -t 200000)
#echo "branching4 n=256 boolector input-limit 2 less-input"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching4.m --unroll 256 -p --solver boolector --find-bounds --input-limit 2 --less-input -t 200000)

echo "branching4 n=256 z3 input-limit 2"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching4.m --unroll 256 -p --solver z3 --find-bounds --input-limit 2 -t 200000)
echo "branching4 n=256 z3 input-limit 2 less-input"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching4.m --unroll 256 -p --solver z3 --find-bounds --input-limit 2 --less-input -t 200000)

echo "branching4 n=256 boolector input-limit 1"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching4.m --unroll 256 -p --solver boolector --find-bounds --input-limit 1 -t 200000)
echo "branching4 n=256 boolector input-limit 1 less-input"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching4.m --unroll 256 -p --solver boolector --find-bounds --input-limit 1 --less-input -t 200000)

echo "branching4 n=256 z3 input-limit 1"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching4.m --unroll 256 -p --solver z3 --find-bounds --input-limit 1 -t 200000)
echo "branching4 n=256 z3 input-limit 1 less-input"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching4.m --unroll 256 -p --solver z3 --find-bounds --input-limit 1 --less-input -t 200000)

echo "branching6 n=256 boolector input-limit 2"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching6.m --unroll 256 -p --solver boolector --find-bounds --input-limit 2 -t 200000)
echo "branching6 n=256 boolector input-limit 2 less-input"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching6.m --unroll 256 -p --solver boolector --find-bounds --input-limit 2 --less-input -t 200000)

echo "branching6 n=256 z3 input-limit 2"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching6.m --unroll 256 -p --solver z3 --find-bounds --input-limit 2 -t 200000)
echo "branching6 n=256 z3 input-limit 2 less-input"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching6.m --unroll 256 -p --solver z3 --find-bounds --input-limit 2 --less-input -t 200000)

echo "branching7 n=512 boolector input-limit 2"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching7.m --unroll 512 -p --solver boolector --find-bounds --input-limit 2 -t 200000)
echo "branching7 n=512 boolector input-limit 2 less-input"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching7.m --unroll 512 -p --solver boolector --find-bounds --input-limit 2 --less-input -t 200000)

echo "branching7 n=512 z3 input-limit 2"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching7.m --unroll 512 -p --solver z3 --find-bounds --input-limit 2 -t 200000)
echo "branching7 n=512 z3 input-limit 2 less-input"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching7.m --unroll 512 -p --solver z3 --find-bounds --input-limit 2 --less-input -t 200000)

echo "branching7 n=512 boolector input-limit 16"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching7.m --unroll 512 -p --solver boolector --find-bounds --input-limit 16 -t 200000)
echo "branching7 n=512 boolector input-limit 16 less-input"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching7.m --unroll 512 -p --solver boolector --find-bounds --input-limit 16 --less-input -t 200000)

echo "branching7 n=512 boolector input-limit 8"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching7.m --unroll 512 -p --solver boolector --find-bounds --input-limit 8 -t 200000)
echo "branching7 n=512 boolector input-limit 8 less-input"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching7.m --unroll 512 -p --solver boolector --find-bounds --input-limit 8 --less-input -t 200000)

echo "branching7 n=512 z3 input-limit 8"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching7.m --unroll 512 -p --solver z3 --find-bounds --input-limit 8 -t 200000)
echo "branching7 n=512 z3 input-limit 8 less-input"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching7.m --unroll 512 -p --solver z3 --find-bounds --input-limit 8 --less-input -t 200000)

echo "insertion-sort n=10000 boolector input-limit 16"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator insertion-sort.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 16 -t 200000)
echo "insertion-sort n=10000 boolector input-limit 16 less-input"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator insertion-sort.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 16 --less-input -t 200000)
'

: '
echo "reservoir-sampling n=10000 boolector input-limit 0"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator reservoir-sampling.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 0 -t 200000 --fast-minimize)
#echo "reservoir-sampling n=10000 boolector input-limit 0 less-input"
#time (gtimeout --foreground -v 35m ../target/release/unicorn beator reservoir-sampling.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 0 --less-input -t 200000)

echo "reservoir-sampling n=10000 boolector input-limit 1"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator reservoir-sampling.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 1 -t 200000 --fast-minimize)
#echo "reservoir-sampling n=10000 boolector input-limit 1 less-input"
#time (gtimeout --foreground -v 35m ../target/release/unicorn beator reservoir-sampling.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 1 --less-input -t 200000)

echo "reservoir-sampling n=10000 boolector input-limit 2"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator reservoir-sampling.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 2 -t 200000 --fast-minimize)
#echo "reservoir-sampling n=10000 boolector input-limit 2 less-input"
#time (gtimeout --foreground -v 35m ../target/release/unicorn beator reservoir-sampling.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 2 --less-input -t 200000)

echo "reservoir-sampling n=10000 boolector input-limit 3"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator reservoir-sampling.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 3 -t 200000 --fast-minimize)

echo "reservoir-sampling n=10000 boolector input-limit 4"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator reservoir-sampling.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 4 -t 200000 --fast-minimize)

echo "reservoir-sampling n=10000 boolector input-limit 5"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator reservoir-sampling.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 5 -t 200000 --fast-minimize)

echo "reservoir-sampling n=10000 boolector input-limit 6"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator reservoir-sampling.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 6 -t 200000 --fast-minimize)

echo "reservoir-sampling n=10000 boolector input-limit 7"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator reservoir-sampling.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 7 -t 200000 --fast-minimize)

echo "reservoir-sampling n=10000 boolector input-limit 8"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator reservoir-sampling.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 8 -t 200000 --fast-minimize)

echo "reservoir-sampling n=10000 boolector input-limit 9"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator reservoir-sampling.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 9 -t 200000 --fast-minimize)

echo "reservoir-sampling n=10000 boolector input-limit 10"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator reservoir-sampling.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 10 -t 200000 --fast-minimize)
'

: '
echo "branching8 n=256 boolector input-limit 1"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching8.m --unroll 256 -p --solver boolector --find-bounds --input-limit 1 -t 200000)
echo "branching8 n=256 boolector input-limit 1 less-input"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching8.m --unroll 256 -p --solver boolector --find-bounds --input-limit 1 --less-input -t 200000)

echo "branching8 n=256 boolector input-limit 2"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching8.m --unroll 256 -p --solver boolector --find-bounds --input-limit 2 -t 200000)
echo "branching8 n=256 boolector input-limit 2 less-input"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching8.m --unroll 256 -p --solver boolector --find-bounds --input-limit 2 --less-input -t 200000)

echo "branching8 n=256 boolector input-limit 0"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching8.m --unroll 256 -p --solver boolector --find-bounds --input-limit 0 -t 200000 --fast-minimize)
echo "branching8 n=256 boolector input-limit 0 less-input"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching8.m --unroll 256 -p --solver boolector --find-bounds --input-limit 0 --less-input -t 200000 --fast-minimize)

echo "branching8 n=256 boolector input-limit 1"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching8.m --unroll 256 -p --solver boolector --find-bounds --input-limit 1 -t 200000 --fast-minimize)
echo "branching8 n=256 boolector input-limit 1 less-input"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching8.m --unroll 256 -p --solver boolector --find-bounds --input-limit 1 --less-input -t 200000 --fast-minimize)

echo "branching8 n=256 boolector input-limit 2"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching8.m --unroll 256 -p --solver boolector --find-bounds --input-limit 2 -t 200000 --fast-minimize)
echo "branching8 n=256 boolector input-limit 2 less-input"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching8.m --unroll 256 -p --solver boolector --find-bounds --input-limit 2 --less-input -t 200000 --fast-minimize)

echo "branching8 n=256 boolector input-limit 3"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching8.m --unroll 256 -p --solver boolector --find-bounds --input-limit 3 -t 200000 --fast-minimize)
echo "branching8 n=256 boolector input-limit 3 less-input"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching8.m --unroll 256 -p --solver boolector --find-bounds --input-limit 3 --less-input -t 200000 --fast-minimize)

echo "branching8 n=256 boolector input-limit 4"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching8.m --unroll 256 -p --solver boolector --find-bounds --input-limit 4 -t 200000 --fast-minimize)
echo "branching8 n=256 boolector input-limit 4 less-input"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching8.m --unroll 256 -p --solver boolector --find-bounds --input-limit 4 --less-input -t 200000 --fast-minimize)

echo "branching8 n=256 boolector input-limit unlimited"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching8.m --unroll 256 -p --solver boolector --find-bounds -t 200000 --fast-minimize)
'

: '
echo "branching9 n=10000 boolector input-limit 0"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching9.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 0 -t 200000 --fast-minimize)
echo "branching9 n=10000 boolector input-limit 0 less-input"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching9.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 0 --less-input -t 200000 --fast-minimize)

echo "branching9 n=10000 boolector input-limit 1"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching9.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 1 -t 200000 --fast-minimize)
echo "branching9 n=10000 boolector input-limit 1 less-input"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching9.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 1 --less-input -t 200000 --fast-minimize)

echo "branching9 n=10000 boolector input-limit 2"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching9.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 2 -t 200000 --fast-minimize)
echo "branching9 n=10000 boolector input-limit 2 less-input"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching9.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 2 --less-input -t 200000 --fast-minimize)

echo "branching9 n=10000 boolector input-limit 3"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching9.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 3 -t 200000 --fast-minimize)
echo "branching9 n=10000 boolector input-limit 3 less-input"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching9.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 3 --less-input -t 200000 --fast-minimize)


echo "branching10 n=10000 boolector input-limit 0"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching10.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 0 -t 200000 --fast-minimize)
echo "branching10 n=10000 boolector input-limit 0 less-input"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching10.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 0 --less-input -t 200000 --fast-minimize)

echo "branching10 n=10000 boolector input-limit 1"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching10.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 1 -t 200000 --fast-minimize)
echo "branching10 n=10000 boolector input-limit 1 less-input"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching10.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 1 --less-input -t 200000 --fast-minimize)

echo "branching10 n=10000 boolector input-limit 2"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching10.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 2 -t 200000 --fast-minimize)
echo "branching10 n=10000 boolector input-limit 2 less-input"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching10.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 2 --less-input -t 200000 --fast-minimize)

echo "branching11 n=10000 boolector input-limit 0"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching11.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 0 -t 200000 --fast-minimize)
echo "branching11 n=10000 boolector input-limit 0 less-input"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching11.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 0 --less-input -t 200000 --fast-minimize)

echo "branching11 n=10000 boolector input-limit 1"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching11.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 1 -t 200000 --fast-minimize)
echo "branching11 n=10000 boolector input-limit 1 less-input"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching11.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 1 --less-input -t 200000 --fast-minimize)

echo "branching11 n=10000 boolector input-limit 2"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching11.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 2 -t 200000 --fast-minimize)
echo "branching11 n=10000 boolector input-limit 2 less-input"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching11.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 2 --less-input -t 200000 --fast-minimize)

echo "branching12 n=10000 boolector input-limit 0"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching12.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 0 -t 200000 --fast-minimize)
echo "branching12 n=10000 boolector input-limit 0 less-input"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching12.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 0 --less-input -t 200000 --fast-minimize)

echo "branching12 n=10000 boolector input-limit 1"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching12.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 1 -t 200000 --fast-minimize)
echo "branching12 n=10000 boolector input-limit 1 less-input"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching12.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 1 --less-input -t 200000 --fast-minimize)

echo "branching12 n=10000 boolector input-limit 2"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching12.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 2 -t 200000 --fast-minimize)
echo "branching12 n=10000 boolector input-limit 2 less-input"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching12.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 2 --less-input -t 200000 --fast-minimize)

echo "branching12 n=10000 boolector input-limit 3"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching12.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 3 -t 200000 --fast-minimize)
echo "branching12 n=10000 boolector input-limit 3 less-input"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching12.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 3 --less-input -t 200000 --fast-minimize)
'

: '
echo "branching13 n=10000 boolector input-limit 0"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching13.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 0 -t 200000 --fast-minimize)

echo "branching13 n=10000 boolector input-limit 1"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching13.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 1 -t 200000 --fast-minimize)

echo "branching13 n=10000 boolector input-limit 2"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching13.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 2 -t 200000 --fast-minimize)


echo "branching14 n=10000 boolector input-limit 0"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching14.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 0 -t 200000 --fast-minimize)

echo "branching14 n=10000 boolector input-limit 1"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching14.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 1 -t 200000 --fast-minimize)

echo "branching14 n=10000 boolector input-limit 2"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching14.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 2 -t 200000 --fast-minimize)
'

: '
echo "reservoir-sampling1 n=10000 boolector input-limit 0"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator reservoir-sampling1.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 0 -t 200000 --fast-minimize)

echo "reservoir-sampling1 n=10000 boolector input-limit 1"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator reservoir-sampling1.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 1 -t 200000 --fast-minimize)

echo "reservoir-sampling1 n=10000 boolector input-limit 2"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator reservoir-sampling1.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 2 -t 200000 --fast-minimize)

echo "reservoir-sampling1 n=10000 boolector input-limit 3"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator reservoir-sampling1.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 3 -t 200000 --fast-minimize)

echo "reservoir-sampling1 n=10000 boolector input-limit 4"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator reservoir-sampling1.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 4 -t 200000 --fast-minimize)

echo "reservoir-sampling1 n=10000 boolector input-limit 5"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator reservoir-sampling1.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 5 -t 200000 --fast-minimize)

echo "reservoir-sampling1 n=10000 boolector input-limit 6"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator reservoir-sampling1.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 6 -t 200000 --fast-minimize)

echo "reservoir-sampling1 n=10000 boolector input-limit 7"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator reservoir-sampling1.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 7 -t 200000 --fast-minimize)

echo "reservoir-sampling1 n=10000 boolector input-limit 8"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator reservoir-sampling1.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 8 -t 200000 --fast-minimize)

echo "reservoir-sampling1 n=10000 boolector input-limit 9"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator reservoir-sampling1.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 9 -t 200000 --fast-minimize)

echo "reservoir-sampling1 n=10000 boolector input-limit 10"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator reservoir-sampling1.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 10 -t 200000 --fast-minimize)

echo "insertion-sort n=10000 boolector input-limit 0"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator insertion-sort.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 0 -t 200000)
'

: '
echo "insertion-sort n=10000 boolector input-limit 1"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator insertion-sort.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 1 -t 200000)

echo "insertion-sort n=10000 boolector input-limit 2"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator insertion-sort.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 2 -t 200000)

echo "insertion-sort n=10000 boolector input-limit 3"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator insertion-sort.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 3 -t 200000)

#echo "insertion-sort n=10000 boolector input-limit 4"
#time (gtimeout --foreground -v 35m ../target/release/unicorn beator insertion-sort.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 4 -t 200000)

#echo "insertion-sort n=10000 boolector input-limit 8"
#time (gtimeout --foreground -v 35m ../target/release/unicorn beator insertion-sort.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 8 -t 200000)

echo "insertion-sort n=10000 boolector input-limit 12"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator insertion-sort.m --unroll 10000 -p --solver boolector --find-bounds --input-limit 12 -t 200000)
'

: '
i=4

while [ $i -le 32 ]
do
  echo "insertion-sort1 n=10000 boolector input-limit $i"
  time (gtimeout --foreground -v 35m ../target/release/unicorn beator insertion-sort1.m --unroll 10000 -p --solver boolector --find-bounds --input-limit $i -t 200000 --fast-minimize)
  ((i += 4))
done
'

: '
i=0

while [ $i -le 2 ]
do
  echo "tiny-program-good-performance n=200 boolector input-limit $i"
  time (gtimeout --foreground -v 35m ../target/release/unicorn beator tiny-program-good-performance.m --unroll 256 -p --solver boolector --find-bounds --input-limit $i -t 200000 --fast-minimize)
  ((i += 1))
done

i=0

while [ $i -le 2 ]
do
  echo "tiny-program-bad-performance n=200 boolector input-limit $i"
  time (gtimeout --foreground -v 35m ../target/release/unicorn beator tiny-program-bad-performance.m --unroll 256 -p --solver boolector --find-bounds --input-limit $i -t 200000 --fast-minimize)
  ((i += 1))
done

i=0

while [ $i -le 3 ]
do
  echo "microbenchmark n=10000 z3 input-limit $i"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator microbenchmark.m --unroll 10000 -p --solver z3 --find-bounds --input-limit $i -t 200000 --fast-minimize)
  ((i += 1))
done
'

: '
i=0

while [ $i -le 8 ]
do
  echo "microbenchmark n=256 boolector input-limit $i"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator microbenchmark.m --unroll 256 -p --solver boolector --find-bounds --input-limit $i -t 200000 --fast-minimize --one-query -v error)
  ((i += 1))
done
'

: '
i=0

while [ $i -le 2 ]
do
  echo "tiny-program-good-performance n=256 boolector input-limit $i"
  time (gtimeout --foreground -v 35m ../target/release/unicorn beator tiny-program-good-performance.m --unroll 256 -p --solver boolector --input-limit $i -t 200000 --fast-minimize --out biere/tiny-program-good-performance-il${i}.btor2)
  ((i += 1))
done

i=0

while [ $i -le 2 ]
do
  echo "tiny-program-bad-performance n=256 boolector input-limit $i"
  time (gtimeout --foreground -v 35m ../target/release/unicorn beator tiny-program-bad-performance.m --unroll 256 -p --solver boolector --input-limit $i -t 200000 --fast-minimize --out biere/tiny-program-bad-performance-il${i}.btor2)
  ((i += 1))
done

i=0

while [ $i -le 3 ]
do
  echo "microbenchmark n=256 boolector input-limit $i"
  time (gtimeout --foreground -v 35m ../target/release/unicorn beator microbenchmark.m --unroll 256 -p --solver boolector --input-limit $i -t 200000 --fast-minimize --out biere/microbenchmark-il${i}.btor2)
  ((i += 1))
done

i=0

while [ $i -le 12 ]
do
  echo "insertion-sort1 n=10000 boolector input-limit $i"
  time (gtimeout --foreground -v 35m ../target/release/unicorn beator insertion-sort1.m --unroll 10000 -p --solver boolector --input-limit $i -t 200000 --fast-minimize --out biere/insertion-sort-il${i}.btor2)
  ((i += 8))
done

echo "insertion-sort1 n=10000 boolector input-limit 2"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator insertion-sort1.m --unroll 10000 -p --solver boolector --input-limit 2 -t 200000 --fast-minimize --out biere/insertion-sort-il2.btor2)

echo "insertion-sort1 n=10000 boolector input-limit 4"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator insertion-sort1.m --unroll 10000 -p --solver boolector --input-limit 4 -t 200000 --fast-minimize --out biere/insertion-sort-il4.btor2)

echo "insertion-sort1 n=10000 boolector input-limit 12"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator insertion-sort1.m --unroll 10000 -p --solver boolector --input-limit 12 -t 200000 --fast-minimize --out biere/insertion-sort-il12.btor2)
'

: '
i=0

while [ $i -le 8 ]
do
  echo "insertion-sort1 n=10000 boolector input-limit $i"
  time (gtimeout --foreground -v 35m ../target/release/unicorn beator insertion-sort1.m --unroll 10000 -p --solver boolector --find-bounds --input-limit $i -t 200000 --fast-minimize --one-query -v error)
  ((i += 1))
done
'

i=0

while [ $i -le 8 ]
do
  echo "microbenchmark n=256 z3 input-limit $i"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator microbenchmark.m --unroll 256 -p --solver z3 --find-bounds --input-limit $i -t 200000 --one-query -v error)
  ((i += 1))
done

: '
i=0

while [ $i -le 8 ]
do
  echo "insertion-sort1 n=10000 z3 input-limit $i"
  time (gtimeout --foreground -v 35m ../target/release/unicorn beator insertion-sort1.m --unroll 10000 -p --solver z3 --find-bounds --input-limit $i -t 200000 --fast-minimize --one-query -v error)
  ((i += 1))
done
'

: '
i=0

while [ $i -le 8 ]
do
  echo "insertion-sort1 n=10000 z3 input-limit $i"
  time (gtimeout --foreground -v 35m ../target/release/unicorn beator insertion-sort1.m --unroll 10000 -p --solver z3 --find-bounds --input-limit $i -t 200000 --fast-minimize -v error)
  ((i += 1))
done

i=0

while [ $i -le 32 ]
do
  echo "insertion-sort2 n=10000 z3 input-limit $i"
  time (gtimeout --foreground -v 35m ../target/release/unicorn beator insertion-sort2.m --unroll 10000 -p --solver z3 --find-bounds --input-limit $i -t 200000 --fast-minimize -v error)
  ((i += 4))
done
'

: '
i=0

while [ $i -le 8 ]
do
  echo "insertion-sort1 n=10000 boolector input-limit $i"
  time (gtimeout --foreground -v 35m ../target/release/unicorn beator insertion-sort1.m --unroll 10000 -p --solver boolector --find-bounds --input-limit $i -t 200000 --fast-minimize -v error)
  ((i += 1))
done


i=0

while [ $i -le 32 ]
do
  echo "insertion-sort2 n=10000 boolector input-limit $i"
  time (gtimeout --foreground -v 35m ../target/release/unicorn beator insertion-sort2.m --unroll 10000 -p --solver boolector --find-bounds --input-limit $i -t 200000 --fast-minimize -v error)
  ((i += 4))
done
'
