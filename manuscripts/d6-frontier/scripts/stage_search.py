"""Exhaustive search for pair-insertion programs at a stage of the six-clique construction
(six-clique-prescribed-ends, Section 4, Lemma 4).  Sites 0..5 (U), pair x = 6, y = 7;
D = clique edges present at the stage, blanks0 = the two stage blanks; contacts = the
sites the pair sees; pre = spokes present initially (a two-spoke seed row).  Moves: Fan
grouped transfers along missing spokes, worst case for blank counts (exterior never
blank), branching on every donor; success = all spokes inserted, all counts restored."""
import itertools, sys
from functools import lru_cache

def search(D, blanks0, contacts, pre=(), xy=False, b_pair=(1, 1)):
    base_adj = {v: set() for v in range(8)}
    for a, b in D:
        base_adj[a].add(b); base_adj[b].add(a)
    if xy:
        base_adj[6].add(7); base_adj[7].add(6)
    b0 = [1] * 8
    for h in blanks0: b0[h] = 0
    b0[6], b0[7] = b_pair
    spokes = [(f, u) for f in (6, 7) for u in contacts if (f, u) not in pre]
    for f, u in pre:
        base_adj[f].add(u); base_adj[u].add(f)
    idx = {s: i for i, s in enumerate(spokes)}
    full = (1 << len(spokes)) - 1
    target = tuple(b0)
    def nbrs(v, ins):
        s = set(base_adj[v])
        for (f, u), i in idx.items():
            if ins >> i & 1:
                if v == f: s.add(u)
                elif v == u: s.add(f)
        return s
    @lru_cache(maxsize=None)
    def win(ins, b):
        if ins == full:
            return b == target
        for v in range(8):
            held = [ (u if v == f else f) for (f, u), i in idx.items() if not ins >> i & 1 and v in (f, u)]
            if not held: continue
            blanks = sum(1 for w in nbrs(v, ins) if b[w] == 0)
            cands = [w for w in held if b[w] >= 1]
            for r in range(1, len(cands) + 1):
                for S in itertools.combinations(cands, r):
                    tot = sum(b[w] for w in S)
                    if tot <= blanks or any(tot - b[t] > blanks for t in S):
                        continue
                    if all(win(ins | (1 << idx[(v, t) if v >= 6 else (t, v)]),
                               tuple(b[i] + (1 if i == v else -1 if i == t else 0) for i in range(8)))
                           for t in S):
                        return True
        return False
    return win(0, tuple(b0))

# ---------------------------------------------------------------------------
# Full-pair programs at the three stages of six-clique Theorem 1 (Proposition 10).
STAGES = {
    'stage 1 (D0, blanks 0,1)': ([(2, 3), (4, 5)], (0, 1)),
    'stage 2 (D1, blanks 2,3)': ([(2, 3), (4, 5), (0, 2), (1, 3)], (2, 3)),
    'stage 3 (D2, blanks 4,5)': ([(2, 3), (4, 5), (0, 2), (1, 3), (1, 4), (0, 1), (0, 3), (3, 5)], (4, 5)),
}

def full_pair_report():
    print("Sanity check: six-clique Lemma 4 is re-found by the search")
    for xy in (False, True):
        print("  type-0 pair, stage 1, seed row x2y, xy present =", xy, ":",
              search([(2, 3), (4, 5)], (0, 1), [1, 2, 3, 4, 5], pre=((6, 2), (7, 2)), xy=xy))
        print("  type-2 pair, stage 2, seed row x0y, xy present =", xy, ":",
              search([(2, 3), (4, 5), (0, 2), (1, 3)], (2, 3), [0, 1, 3, 4, 5], pre=((6, 0), (7, 0)), xy=xy))
    print("Full pairs (x, y adjacent to all six sites):")
    for name, (D, bl) in STAGES.items():
        for xy in (False, True):
            res = [search(D, bl, range(6), xy=xy)]
            for p in range(6):
                res.append(search(D, bl, range(6), pre=((6, p), (7, p)), xy=xy))
            print("  ", name, "xy present =", xy, ": program with no seed row:", res[0],
                  "; with a two-spoke seed row x p y for some p:", any(res[1:]))

if __name__ == '__main__' and len(__import__('sys').argv) > 1 and __import__('sys').argv[1] == 'fullpair':
    full_pair_report()
