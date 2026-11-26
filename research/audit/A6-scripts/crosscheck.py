"""Cross-check: candidate roots derived from the recomputed banks (sevensite) +
K2 refinement + BS (subcubic) + one-universal bank, versus the RS table (census.py)."""
import itertools
from census import cands, pairs
from sevensite import CORES
SURV = {'K0': set(), 'K1': {(0, 1, 4)}, 'K2': {(0, 1, 3), (0, 1, 2, 3, 4)},   # after refinement
        'K3': {A for k in (3, 4, 5) for A in itertools.combinations(range(5), k)}}
Kedges = {name: set(frozenset(e) for e in CORES[name]) for name in SURV}
perms = list(itertools.permutations(range(5)))
mismatch = 0; tot = 0
for s in range(1 << 15):
    C = set(pairs[i] for i in range(15) if s >> i & 1)
    table = set(cands(sorted(C)))
    derived = set()
    for r in range(6):
        T = [v for v in range(6) if v != r]
        A = [t for t in T if tuple(sorted((r, t))) in C]
        if not A:
            # isolated root: candidate iff C-r in {K5, K5-e, K5-P3}  (bank: K0 excluded; K1..K3 remain)
            K = [p for p in C if r not in p]
            deg = {t: sum(1 for p in K if t in p) for t in T}
            nuni = sum(1 for t in T if deg[t] == 4)
            if nuni >= 2:
                # identify core
                for name in ('K1', 'K2', 'K3'):
                    if len(K) == len(Kedges[name]): derived.add(r)
            continue
        K = [p for p in C if r not in p]
        deg = {t: sum(1 for p in K if t in p) for t in T}
        nuni = sum(1 for t in T if deg[t] == 4)
        if nuni <= 1: continue  # BS or one-universal bank: passes
        Kset = set(frozenset(p) for p in K)
        found = False
        for name in ('K0', 'K1', 'K2', 'K3'):
            if len(Kset) != len(Kedges[name]): continue
            for pm in perms:
                mp = dict(zip(T, pm))
                if set(frozenset((mp[x], mp[y])) for x, y in K) == Kedges[name]:
                    if tuple(sorted(mp[t] for t in A)) in SURV[name]: derived.add(r)
                    found = True; break
            if found: break
        assert found
    tot += 1
    if derived != table: mismatch += 1
print('cores checked', tot, 'mismatches between bank-derived and printed table:', mismatch)
