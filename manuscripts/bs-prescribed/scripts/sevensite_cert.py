"""Seven-site certificates for the floor bound with five even vertices and one universal vertex.

Model (independent re-implementation of audit A6's seven-site search, in the exact semantics of
the Lean checker `Prog.ok`, lean/GallaiLean/Schedule.lean):
  vertices 0..4 = T, the five even vertices of W, with 0 = x universal in K = W[T];
  5 = u, an odd vertex with A = N(u) & T nonempty; 6 = v, an odd neighbour of u with no
  neighbour in T.  All other vertices of W are odd and are never touched.
Local edges: the core K, u-A, u-v.  A seed holds a set H of local edges such that exactly one
model vertex has even degree in W - H (parity is then forced for the rest: N is odd).  Lovasz
(lovasz_ends) gives exact ends: 0 there, 1 at every other vertex.  A move offers a donor list ds
(held edges t-r, t in ds) to a receiver r; it is legal when the number of present model
neighbours of r with 0 ends is smaller than the sum of the donors' ends; every donor with a
positive end count is a branch (Fan's grouped lemma, `Ach.grouped`).  A certificate restores all
of H; the final partition has (N-1)/2 paths since the sum of ends never changes.

Usage: python3 sevensite_cert.py [CORE ...]   (cores: E0 K2 P3 K3 M P C); prints certificates
and writes certs.json next to this script.
"""
import itertools
import json
import os
import sys
from functools import lru_cache

CORES = {
    'E0': [],
    'K2': [(1, 2)],
    'P3': [(1, 2), (2, 3)],
    'K3': [(1, 2), (2, 3), (1, 3)],
    'M': [(1, 2), (3, 4)],
    'P': [(1, 2), (2, 3), (3, 4)],
    'C': [(1, 2), (2, 3), (3, 4), (4, 1)],
}
NM = 'xabcduv'
U, V = 5, 6


def local_edges(core, A):
    E = [(0, t) for t in (1, 2, 3, 4)] + list(CORES[core])
    E += [(t, U) for t in A] + [(U, V)]
    return [tuple(sorted(e)) for e in E]


def search(E, H):
    """AND-OR search; returns a program tree or None.
    Tree: ('done',) or ('offer', ds, r, {t: subtree})."""
    n = 7
    held = list(H)
    present0 = [e for e in E if e not in H]
    par = [0, 0, 0, 0, 0, 1, 1]
    for a, b in H:
        par[a] ^= 1
        par[b] ^= 1
    if sum(1 for p in par if p == 0) != 1:
        return None
    c0 = tuple(p for p in par)  # 1 on odd, 0 on the even one

    @lru_cache(maxsize=None)
    def rec(mask, c):
        if mask == (1 << len(held)) - 1:
            return ('done',)
        adj = set(present0) | {held[i] for i in range(len(held)) if mask >> i & 1}
        for r in range(n):
            cand = [(held[i][0] if held[i][1] == r else held[i][1], i)
                    for i in range(len(held)) if not (mask >> i & 1) and r in held[i]]
            if not cand:
                continue
            blank = sum(1 for a in range(n) if a != r and tuple(sorted((a, r))) in adj and c[a] == 0)
            sat = []
            for k in range(1, len(cand) + 1):
                for S in itertools.combinations(cand, k):
                    if sum(c[t] for t, _ in S) <= blank:
                        continue
                    if any(set(T) <= set(S) for T in sat):
                        continue
                    sat.append(S)
                    kids = {}
                    ok = True
                    for t, i in S:
                        if c[t] == 0:
                            continue
                        nc = list(c); nc[t] -= 1; nc[r] += 1
                        sub = rec(mask | (1 << i), tuple(nc))
                        if sub is None:
                            ok = False
                            break
                        kids[t] = sub
                    if ok:
                        return ('offer', [t for t, _ in S], r, kids)
        return None

    return rec(0, c0), c0


def find(core, A, maxH=None):
    E = local_edges(core, A)
    for k in range(0, len(E) + 1):
        if maxH is not None and k > maxH:
            break
        for H in itertools.combinations(E, k):
            out = search(E, list(H))
            if out is None:
                continue
            tree, c0 = out
            if tree is not None:
                return {'core': core, 'A': list(A), 'E': E, 'H': list(H), 'c0': list(c0),
                        'tree': tree}
    return None


def fmt(t, ind=2):
    if t[0] == 'done':
        return ' ' * ind + 'done\n'
    _, ds, r, kids = t
    s = ' ' * ind + f"offer {''.join(NM[d] for d in ds)} -> {NM[r]}\n"
    for d, sub in kids.items():
        if len(ds) > 1:
            s += ' ' * ind + f"[{NM[d]} returned]\n"
        s += fmt(sub, ind + (2 if len(ds) > 1 else 0))
    return s


def main():
    cores = sys.argv[1:] or list(CORES)
    allc = []
    for core in cores:
        bad = []
        for k in range(1, 6):
            for A in itertools.combinations(range(5), k):
                c = find(core, A)
                tag = ''.join(NM[t] for t in A)
                if c is None:
                    bad.append(tag)
                    print(core, tag, 'NO CERTIFICATE', flush=True)
                    continue
                allc.append(c)
                print(core, 'A=' + tag, 'held', ' '.join(NM[a] + NM[b] for a, b in c['H']),
                      'seed-even', NM[c['c0'].index(0)], flush=True)
                print(fmt(c['tree']), end='')
        print(core, 'uncertified:', bad, flush=True)
    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'certs.json'), 'w') as f:
        json.dump(allc, f)


if __name__ == '__main__':
    main()
