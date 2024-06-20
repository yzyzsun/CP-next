#!/bin/bash

for f in comparison/{fib,fact,sieve,nbody}.mjs; do
  node start.mjs $f
done

for i in $(seq 0 10); do
  f="comparison/region_$i.mjs"
  sed "s/{{i}}/$i/" comparison/region.mjs > $f
  node start.mjs $f
  rm -f $f
done

for i in $(seq 0 10); do
  f="comparison/region_$i.ts"
  sed "s/{{i}}/$i/" comparison/region.ts > $f.ts
  tsc $f.ts
  node start.mjs $f.js
  rm -f $f.{ts,js}
done

spago run --node-args "comparison/*.cp"
if [ $? -eq 0 ]; then
    for i in $(seq 0 10); do
    f="comparison/region_$i.cp.mjs"
    node start.mjs $f
  done
fi
rm -f comparison/*.cp.{h,mjs}
