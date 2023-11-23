#!/bin/bash
i=1

while [ $i -le 300 ]
do
  echo $i
  ../target/debug/unicorn beator branching2.m --unroll $i --prune --solver boolector
  ((i++))
done
