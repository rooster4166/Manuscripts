#!/bin/sh
# Build ptm_pee: ptm.c with each failure of the all-ends prescription (PEE) printed as
# "PEEFAIL g6 e1 e2 ..." (the prescribed short ends, in F order).  Used for the E24(J) cross-check:
#   ./ptm_pee.sh && ./ptm_pee f 3 0 1 < out/d6_9_simple.txt | grep PEEFAIL
cd "$(dirname "$0")"
sed 's/      if (r == 0) cnt_pee_fail++;/      if (r == 0) { cnt_pee_fail++; printf("PEEFAIL %s", cur_g6); for (int k = 0; k < nf; k++) printf(" %d", (c >> k) \& 1 ? fb[k] : fa[k]); printf("\\n"); }/' ptm.c > ptm_pee.c
gcc -O2 -o ptm_pee ptm_pee.c
