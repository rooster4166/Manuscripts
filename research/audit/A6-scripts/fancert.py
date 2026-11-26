"""Independent AND-OR search for Fan-restoration certificates on a local record.

Local vertices 0..n-1 with known mutual adjacency (edge list E) and known parity
in the host.  All other (external) vertices are odd with exactly one end, are
never blank, and never take part in held edges.  A seed holds a set H of local
edges; after removal the parity vector must be acceptable for the chosen seed
type; initial ends are exact (Lovasz).  Moves: receiver x, donor set S of
vertices y with xy in H unrestored, sum b(y) > Z(x) where Z(x) counts present
local neighbours of x with zero ends.  Each y in S with b(y)>0 is a child.
"""
import itertools
from functools import lru_cache

def search(n, E, H, b0, goal=None, maxS=None):
    """E: list of local edges (pairs), H: list of held edges (subset of E).
    b0: initial end vector (tuple).  goal(b) -> bool on the final vector
    (None means any final vector).  Returns a certificate tree or None."""
    Hidx = {frozenset(e): i for i, e in enumerate(H)}
    present0 = set(frozenset(e) for e in E) - set(Hidx)
    nb_present0 = [0] * n
    for e in present0:
        a, b = tuple(e)
        nb_present0[a] |= 1 << b
        nb_present0[b] |= 1 << a
    held_at = [[] for _ in range(n)]  # (other, idx)
    for e, i in Hidx.items():
        a, b = tuple(e)
        held_at[a].append((b, i))
        held_at[b].append((a, i))
    full = (1 << len(H)) - 1
    memo = {}

    def present_nb(x, mask):
        m = nb_present0[x]
        for (y, i) in held_at[x]:
            if mask >> i & 1:
                m |= 1 << y
        return m

    def rec(mask, b):
        key = (mask, b)
        if key in memo:
            return memo[key]
        if mask == full:
            ok = True if goal is None else goal(b)
            memo[key] = 'leaf' if ok else None
            return memo[key]
        memo[key] = None  # cycle guard (mask strictly grows so not needed)
        for x in range(n):
            cands = [(y, i) for (y, i) in held_at[x] if not (mask >> i & 1) and b[y] > 0]
            if not cands:
                continue
            pm = present_nb(x, mask)
            Z = sum(1 for w in range(n) if (pm >> w & 1) and b[w] == 0)
            # minimal satisfying donor sets
            sat = []
            for size in range(1, len(cands) + 1):
                if maxS and size > maxS: break
                for S in itertools.combinations(cands, size):
                    if sum(b[y] for y, _ in S) <= Z:
                        continue
                    if any(set(T) <= set(S) for T in sat):
                        continue
                    sat.append(S)
                    kids = []
                    good = True
                    for (y, i) in S:
                        nb = list(b); nb[y] -= 1; nb[x] += 1
                        sub = rec(mask | (1 << i), tuple(nb))
                        if sub is None:
                            good = False; break
                        kids.append(((y, x), sub))
                    if good:
                        memo[key] = ('offer', x, tuple(y for y, _ in S), Z, kids)
                        return memo[key]
        memo[key] = None
        return None
    return rec(0, tuple(b0))
