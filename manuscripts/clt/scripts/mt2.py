"""mt2.py: minimal unsatisfiable constraint systems from `enum -v L` output (session claude/clt).

For each graph the input lists the inclusion-minimal violation sets V(D) over an atom universe
(av(c,a): the path ending at c avoids a; ne(u,v): the paths ending at u, v differ).  A system X
is unsatisfiable iff X meets every V(D).  For atom i let cover[i] be the set of family members
containing i (a bitmask); X is unsatisfiable iff the union of cover[i], i in X, is everything.

Usage: python3 mt2.py K [kinds] [filter] < enum_v_output
  K      : maximum system size
  kinds  : 'a' (avoidance atoms only), 'an' (both)  [default 'a']
  filter : optional Python expression in the variables X (list of atoms (t,x,y)), n, adj, g,
           deg; only systems satisfying it are searched (it should be closed under subsets).
Prints: graph6 n g system
"""
import sys
from itertools import combinations


def parse_g6(s):
    n = ord(s[0]) - 63
    bits = []
    for ch in s[1:]:
        v = ord(ch) - 63
        for k in range(5, -1, -1):
            bits.append((v >> k) & 1)
    adj = [set() for _ in range(n)]
    k = 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]:
                adj[i].add(j)
                adj[j].add(i)
            k += 1
    return n, adj


def blocks(stream):
    cur = None
    for line in stream:
        p = line.split()
        if not p:
            continue
        if p[0] == 'G':
            if cur:
                yield cur
            cur = [p[1], []]
        elif p[0] == 'V':
            atoms = []
            for t in p[1:]:
                kind = t[0]
                x, y = map(int, t[1:].split(','))
                atoms.append((kind, x, y))
            cur[1].append(atoms)
    if cur:
        yield cur


def search(g6, fam, K, kinds, filt=None):
    n, adj = parse_g6(g6)
    deg = [len(a) for a in adj]
    ev = [v for v in range(n) if deg[v] > 0 and deg[v] % 2 == 0]
    g = ev[0] if ev else -1
    if not fam:
        return n, adj, g, [None]           # no Lovász decomposition
    if any(len(f) == 0 for f in fam):
        return n, adj, g, []
    universe = sorted({a for f in fam for a in f if a[0] in kinds})
    cover = {a: 0 for a in universe}
    for j, f in enumerate(fam):
        for a in f:
            if a in cover:
                cover[a] |= 1 << j
    full = (1 << len(fam)) - 1
    found = []
    res = []
    env = {'n': n, 'adj': adj, 'g': g, 'deg': deg}
    # iterative deepening so that reported systems are minimal
    for k in range(1, K + 1):
        def rec2(start, X, cov, k=k):
            if len(X) == k:
                if cov == full and not any(set(r) <= set(X) for r in res):
                    res.append(tuple(X))
                return
            for i in range(start, len(universe)):
                a = universe[i]
                Y = X + [a]
                if filt is not None:
                    env['X'] = Y
                    if not eval(filt, env):
                        continue
                if any(set(r) <= set(Y) for r in res):
                    continue
                rec2(i + 1, Y, cov | cover[a])
        rec2(0, [], 0)
    return n, adj, g, res


def main():
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 2
    kinds = sys.argv[2] if len(sys.argv) > 2 else 'a'
    filt = sys.argv[3] if len(sys.argv) > 3 else None
    for g6, fam in blocks(sys.stdin):
        n, adj, g, res = search(g6, fam, K, kinds, filt)
        for X in res:
            if X is None:
                print(g6, n, g, 'NODECOMP')
            else:
                print(g6, n, g, ' '.join(f'{t}{x},{y}' for t, x, y in X))
        sys.stdout.flush()


if __name__ == '__main__':
    main()
