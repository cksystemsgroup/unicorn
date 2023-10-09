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
'

echo "branching7 n=512 boolector input-limit 8"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching7.m --unroll 512 -p --solver boolector --find-bounds --input-limit 8 -t 200000)
echo "branching7 n=512 boolector input-limit 8 less-input"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching7.m --unroll 512 -p --solver boolector --find-bounds --input-limit 8 --less-input -t 200000)

: '
echo "branching7 n=512 z3 input-limit 8"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching7.m --unroll 512 -p --solver z3 --find-bounds --input-limit 8 -t 200000)
echo "branching7 n=512 z3 input-limit 8 less-input"
time (gtimeout --foreground -v 35m ../target/release/unicorn beator branching7.m --unroll 512 -p --solver z3 --find-bounds --input-limit 8 --less-input -t 200000)
'
