#!/bin/bash
# run11.sh W NW OUTDIR: worker W of NW over the 2000 geng slices of connected order-11 graphs.
# Each slice: nauty-geng -c 11 -q i/2000 | dl -m sum -q > OUTDIR/s_i.txt  (skips slices already done)
W=$1; NW=$2; OUT=$3; DIR=$(dirname "$0")
mkdir -p "$OUT"
for ((i=W; i<2000; i+=NW)); do
  f="$OUT/s_$i.txt"
  if [ -s "$f" ] && grep -q SUMMARY "$f"; then continue; fi
  nauty-geng -c 11 -q $i/2000 | "$DIR/dl" -m sum -q > "$f.tmp" && mv "$f.tmp" "$f"
done
