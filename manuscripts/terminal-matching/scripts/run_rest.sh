#!/bin/sh
# Resumable runner for the last six order-10 chunks (out/n10/rest.txt split into out/n10/rp/p_00..39):
# runs `ptm f 2 2000000 0` on every piece whose .out has no SUMMARY line yet, 4 at a time.
cd "$(dirname "$0")"
for f in out/n10/rp/p_??; do grep -q SUMMARY "$f.out" 2>/dev/null || echo "$f"; done |
  xargs -P 4 -I{} sh -c 'nice -n 10 ./ptm f 2 2000000 0 < {} > {}.tmp && mv {}.tmp {}.out'
