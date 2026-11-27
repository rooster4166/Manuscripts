"""tb_ls.py: triangle bases (direct-test1 Conj 3.1) by local search (session claude/clt).

For J (z = its unique even vertex), a root r in N(z), every data choice (w, M0) and every
orientation of the m disjunctions, build M = J - zw - {z a_i, z b_i, a_i b_i} (z a leaf at r, w the
only even vertex) and look for a Lovász decomposition of M with a_i not in Q(b_i) (or the reverse,
per the orientation) by the exact DFS with a small budget and then the local search lsls.py.
Positive answers only; every base is checked independently (clt_lib.check).

usage: tb_ls.py edges FILE LINE      (a 'NO BASE n [edge list] r R' line of the triangle-base logs)
       tb_ls.py resid G6 R           (B = J - z on vertices 0..n-1 with N(z) = {0..5}; root R in B)
Prints the base (paths of M, vertex numbering of J) or 'not found'.
"""
import ast
import itertools
import sys
from clt_lib import parse_g6, solve_many, check
from lsls import search


def pms(vs, adj):
    if not vs:
        yield []
        return
    a = vs[0]
    for b in vs[1:]:
        if b in adj[a]:
            for pm in pms([v for v in vs[1:] if v != b], adj):
                yield [(a, b)] + pm


def run(n, adj, z, r, steps=3000, budget=20000):
    U = sorted(adj[z])
    tried = 0
    for w in U:
        if w == r:
            continue
        for pm in pms([u for u in U if u not in (r, w)], adj):
            M = [set(a) for a in adj]
            def rm(a, b):
                M[a].discard(b)
                M[b].discard(a)
            rm(z, w)
            for a, b in pm:
                rm(z, a); rm(z, b); rm(a, b)
            ev = [v for v in range(n) if M[v] and len(M[v]) % 2 == 0]
            assert ev == [w] or (ev == [] and not M[w]), (ev, w)
            for orient in itertools.product((0, 1), repeat=len(pm)):
                ef = {}
                for (a, b), o in zip(pm, orient):
                    c, x = (a, b) if o == 0 else (b, a)
                    ef.setdefault(c, set()).add(x)
                sysd = {'ef': ef}
                tried += 1
                st, P = solve_many([(n, M, sysd)], budget=budget)[0]
                if st != 'OK':
                    P = search(n, M, sysd, steps=steps, k=3, seed=tried)
                if P:
                    assert check(n, M, P, sysd)
                    return dict(w=w, pairs=pm, orient=orient, paths=P, tried=tried)
    return {'tried': tried}


def main():
    mode = sys.argv[1]
    if mode == 'edges':
        line = open(sys.argv[2]).read().split('\n')[int(sys.argv[3])]
        p = line.split('[', 1)
        n = int(p[0].split()[2])
        E = ast.literal_eval('[' + p[1].split(']')[0] + ']')
        r = int(p[1].split(']')[1].split()[1])
        adj = [set() for _ in range(n)]
        for a, b in E:
            adj[a].add(b)
            adj[b].add(a)
    else:
        nB, adjB = parse_g6(sys.argv[2])
        n = nB + 1
        adj = [set(a) for a in adjB] + [set()]
        for u in range(6):
            adj[nB].add(u)
            adj[u].add(nB)
        r = int(sys.argv[3])
    ev = [v for v in range(n) if adj[v] and len(adj[v]) % 2 == 0]
    assert len(ev) == 1, ev
    z = ev[0]
    assert r in adj[z]
    res = run(n, adj, z, r)
    if 'paths' in res:
        print(f"FOUND n={n} z={z} r={r} w={res['w']} pairs={res['pairs']} orient={res['orient']} "
              f"(data/orientations tried: {res['tried']})")
        for P in res['paths']:
            print(' '.join(map(str, P)))
    else:
        print(f"not found (data/orientations tried: {res['tried']})")


if __name__ == '__main__':
    main()
