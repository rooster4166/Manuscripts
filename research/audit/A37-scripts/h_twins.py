"""h_twins.py (audit A37): per instance with matching (DL) data, is EVERY data choice (w, M0) a
universal-twin choice?  Compared with 'J - z is an odd semi-clique'.  Own code.
usage: python3 h_twins.py FILE [SAMPLE SEED]"""
import gzip, random, sys
from collections import Counter
sys.path.insert(0, __file__.rsplit("/", 1)[0])
from a37lib import adjacency, delete_vertex, g6_decode
from h_bases8 import perfect_matchings, univ_twins
fn = sys.argv[1]
op = gzip.open if fn.endswith(".gz") else open
lines = op(fn, "rt").read().splitlines()
if len(sys.argv) > 2:
    lines = random.Random(int(sys.argv[3])).sample(lines, int(sys.argv[2]))
st = Counter()
for line in lines:
    g6, z, r = line.split()[:3]; z, r = int(z), int(r)
    n, E = g6_decode(g6); A = adjacency(n, E); B = delete_vertex(E, z)
    k = (n - 2) // 2; semi = len(B) > 2 * k * k
    T = sorted(A[z]); tot = twin = 0
    for w in T:
        if w == r: continue
        for pm in perfect_matchings([v for v in T if v not in (r, w)], A):
            G = B - {frozenset(p) for p in pm}
            tot += 1; twin += any(univ_twins(n, G, a, c) for a, c in pm)
    if tot == 0: st[("no data", "semi", semi)] += 1; continue
    st[("all data twin", twin == tot, "semi", semi)] += 1
    if twin == tot and not semi: print("ALL-TWIN, not semi:", g6, z, r, "d(z)", len(A[z]), "data choices", tot, flush=True)
for kk in sorted(st, key=str): print(kk, st[kk])
