#!/bin/bash

RED='\033[0;31m'
OFF='\033[0m'

function bench {
  echo -e $RED[$2]$OFF
  cp $1-$2 $1
  spago run --node-args "benchmarks/*.lib"
  spago run --node-args "benchmarks/*.cp"
  if [ $? -eq 0 ]; then
    for f in benchmarks/*.cp.mjs; do
      node start.mjs $f
    done
  fi
  cp $1-base $1
}

for variant in base box dps tyequiv coelim; do
  bench src/CP/CodeGen.purs $variant
done
bench src/CP/Typing.purs projoptim

rm -f benchmarks/*.{lib,cp}.{h,mjs}
