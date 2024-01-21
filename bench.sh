#!/bin/bash

RED='\033[0;31m'
OFF='\033[0m'

purs="src/CP/CodeGen.purs"
variants=(tyequiv coelim dps base)

for variant in "${variants[@]}"; do
  echo -e $RED[$variant]$OFF
  cp $purs.$variant $purs
  spago run --node-args "benchmarks/*.lib"
  spago run --node-args "benchmarks/*.cp"
  if [ $? -eq 0 ]; then
    for file in benchmarks/*.cp.mjs; do
      node start.mjs $file
    done
  fi
done
