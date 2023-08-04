#!/bin/bash
i=1

while [ $i -le 150 ]
do
  echo $i
  ../target/debug/unicorn beator tiny1.m --unroll $i --prune --solver boolector
  ((i++))
done
