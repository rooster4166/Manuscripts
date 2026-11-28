"""allodd_route.py: all-odd DL(2)/DL(3), free and fixed, decided with tools/route_ext.c (test2 session).

Same constraint families as allodd_dl.c (F2, F3, X2, X3, XF, XF2; all pairs non-adjacent, all
vertices distinct).  For a connected graph G with every degree odd, a Lovasz decomposition has
exactly one end at every vertex, and [c|x] means "x is not on Q(c)".  A fixed set (a conjunction of
literals [c|x] with distinct c) is one route_ext query
    WA n m edges  1 ... 1  x_0 ... x_{n-1}      (x_c = {x} for each literal, else 0)
which answers 0 (no such Lovasz decomposition) or 1 with the paths of one.  Each decomposition
returned strikes every standing set it satisfies, in every family.  A free clause ([a|b] or [b|a])
is satisfied by a set iff one of its orientations is, so a free set is decided by querying its
orientations until one succeeds; it fails only if every orientation fails.
Every returned decomposition is checked in Python (path partition of E(G), one end per vertex).
usage: python3 allodd_route.py ROUTE_EXT FAMILIES < graph6     (FAMILIES: subset of 23xyuv)
"""
import itertools
import subprocess
import sys

import networkx as nx


def lit(c, x):
    return (c, x)


def main():
    exe, fams = sys.argv[1], sys.argv[2]
    p = subprocess.Popen(['stdbuf', '-oL', exe], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
    names = {'2': 'F2', '3': 'F3', 'x': 'X2', 'y': 'X3', 'u': 'XF', 'v': 'XF2'}
    tot = {f: 0 for f in fams}
    fail = {f: 0 for f in fams}
    ngraphs = nq = 0
    for g6 in sys.stdin:
        g6 = g6.strip()
        if not g6:
            continue
        G = nx.from_graph6_bytes(g6.encode())
        n = G.number_of_nodes()
        if any(d % 2 == 0 for _, d in G.degree()) or not nx.is_connected(G):
            continue
        ngraphs += 1
        E = list(G.edges())
        head = 'WA %d %d %s %s ' % (n, len(E), ' '.join('%d %d' % e for e in E), ' '.join(['1'] * n))
        pairs = [(a, b) for a in range(n) for b in range(a + 1, n) if not G.has_edge(a, b)]
        # a set = (family, list of clauses); a clause = tuple of literals (an OR)
        sets = []
        def fx(pr, o):
            a, b = pr
            return ((b, a),) if o else ((a, b),)
        def fr(pr):
            a, b = pr
            return ((a, b), (b, a))
        for k in (2, 3):
            for combo in itertools.combinations(pairs, k):
                vs = [v for pr in combo for v in pr]
                if len(set(vs)) != 2 * k:
                    continue
                if k == 2:
                    if '2' in fams:
                        sets.append(('2', [fr(combo[0]), fr(combo[1])]))
                    if 'x' in fams:
                        for o in itertools.product((0, 1), repeat=2):
                            sets.append(('x', [fx(combo[0], o[0]), fx(combo[1], o[1])]))
                    if 'u' in fams:
                        for i in range(2):
                            for o in (0, 1):
                                sets.append(('u', [fx(combo[i], o), fr(combo[1 - i])]))
                else:
                    if '3' in fams:
                        sets.append(('3', [fr(pr) for pr in combo]))
                    if 'y' in fams:
                        for o in itertools.product((0, 1), repeat=3):
                            sets.append(('y', [fx(pr, oo) for pr, oo in zip(combo, o)]))
                    if 'v' in fams:
                        for i in range(3):
                            for o in (0, 1):
                                sets.append(('v', [fx(combo[i], o)] + [fr(combo[j]) for j in range(3) if j != i]))
        for f, _ in sets:
            tot[f] += 1
        standing = sets
        while standing:
            f, cls = standing[0]
            ok = False
            for choice in itertools.product(*cls):
                x = [0] * n
                for c, xx in choice:
                    x[c] |= 1 << xx
                p.stdin.write(head + ' '.join(map(str, x)) + '\n')
                p.stdin.flush()
                ans = p.stdout.readline()
                nq += 1
                if ans.startswith('1'):
                    paths = [list(map(int, s.split())) for s in ans.split('|')[1:] if s.strip()]
                    used, ends = set(), [0] * n
                    for P in paths:
                        assert len(P) >= 2 and len(set(P)) == len(P)
                        for a, b in zip(P, P[1:]):
                            e = frozenset((a, b))
                            assert G.has_edge(a, b) and e not in used
                            used.add(e)
                        ends[P[0]] += 1
                        ends[P[-1]] += 1
                    assert len(used) == len(E) and all(e == 1 for e in ends)
                    onp = {}
                    for P in paths:
                        S = set(P)
                        onp[P[0]] = S
                        onp[P[-1]] = S
                    sat = lambda c, xx: xx not in onp[c]
                    assert all(sat(c, xx) for c, xx in choice)
                    standing = [s for s in standing if not all(any(sat(c, xx) for c, xx in cl) for cl in s[1])]
                    ok = True
                    break
                assert ans.startswith('0'), ans
            if not ok:
                fail[f] += 1
                print('FAIL', names[f], g6, cls, flush=True)
                standing = standing[1:]
    print('graphs', ngraphs, 'queries', nq, file=sys.stderr)
    for f in fams:
        print('%s: sets %d, fail %d' % (names[f], tot[f], fail[f]), file=sys.stderr)


if __name__ == '__main__':
    main()
