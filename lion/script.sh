#!/bin/bash
i=1

while [ $i -le 150 ]
do
  echo $i
  ../target/debug/unicorn beator tiny.m --unroll 1 --solver boolector --out tiny4.btor2
  ((i++))
done
