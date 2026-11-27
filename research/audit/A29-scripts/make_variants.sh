#!/bin/bash
# A29: auditor variants of the authors' code (scratch copies only; the originals are untouched).
# Run from a scratch copy of manuscripts/dl-one/scripts at commit 5d81e14.
set -e
# (1) true L1* local form: keep g in the avoided set when g is not in N(c)
sed 's/if (w == g) Am \&= ~(1u << g);/if (w == g \&\& ((adj0[c] >> g) \& 1)) Am \&= ~(1u << g);/' dl.c > dl_loc.c
gcc -O2 -o dl_loc dl_loc.c
# (2) CN1 'both' mode restricted to d(a), d(b) >= 3
sed 's/        int cn1 = (adj0\[a\] \& adj0\[b\]) == (1u << g);/        int cn1 = (adj0[a] \& adj0[b]) == (1u << g); if (!cn1 || deg(E,a) < 3 || deg(E,b) < 3) continue;/' dl.c > dl_cn1.c
gcc -O2 -o dl_cn1 dl_cn1.c
# (3) dlrec printing both orientations, for the soundness check against dl -m pairs
python3 - <<'PY'
src = open('dlrec.cpp').read()
old = "bool r1 = rec(G, b, 1u << a), r = r1 || rec(G, a, 1u << b);"
new = ("bool r1 = rec(G, b, 1u << a); bool r2 = rec(G, a, 1u << b); "
       "printf(\"ORI %s %d %d %d %d\\n\", line, a, b, (int)r1, (int)r2); bool r = r1 || r2;")
assert old in src
open('dlrec_both.cpp', 'w').write(src.replace(old, new))
PY
g++ -O2 -I ../../l1-induction/scripts -o dlrec_both dlrec_both.cpp
# usage:
#   O=../../stl/scripts; cat $O/one_even_{5,7,9}.g6 > oe579.g6
#   ./dl_loc -m nmax < $O/one_even_9.g6 | tail -1        # local=86882 local_viol=0
#   ./dl_cn1 -m both < $O/one_even_9.g6 | tail -1        # cn1=5458 cn1_noboth=0
#   ./dl -m pairs < oe579.g6 > pairs579.txt ; python3 stats.py pairs579.txt
#   ./dlrec_both BMS < oe579.g6 > ori579.txt ; python3 cert_sound.py ori579.txt pairs579.txt
