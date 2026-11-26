import time, sys
from circ import *
from common import iso_classes_edge_sets
n = int(sys.argv[1]); k = (n-1)//2
t0 = time.time()
Xs = iso_classes_edge_sets(n, k) if n <= 11 else None
ok = 0
for H in Xs:
    X = list(H.edges())
    st, cyc = ham_decomp(n, [[e] for e in X], time_limit=300)
    good = cyc is not None and check(n, cyc, [[e] for e in X])
    ok += good
    if not good: print("FAIL/UNKNOWN", X, st, flush=True)
print(f"n={n}: rainbow found for {ok}/{len(Xs)} classes, {time.time()-t0:.1f}s", flush=True)
