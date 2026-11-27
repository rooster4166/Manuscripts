"""Audit A22c: Conjecture 8.5 (chains) and its link to Definition 8.1 / Lean AdmChain.
For J (z = 0) with N(z) pairwise at distance >= 3 in H = J - z, and each r in N(z), search exactly
(every P2, then BFS for P1 avoiding the edges of P2) for x1 != r and a labelling of the other four
with
  P2: y3 -> x2 in H - N_H[x3] - {x1, y2},
  P1: y2 -> x1 in H - N_H[x2] - N_H[x3]                       ('relaxed' = the conjecture as stated)
  P1 additionally avoiding y3                                  ('strict' = Def 8.1 with N = N_G, Lean)
Families:
  ring   : the ring of six triangles (v_i a_i b_i, links b_i a_{i+1}), order 19, and variants with
           k parallel 'ladders' between consecutive blobs;
  priv   : z + v_1..v_6, two private neighbours each (degree dpriv), the rest random (own code);
usage: conj_check.py ring | priv COUNT SEED EXTRA DPRIV"""
import sys, random, itertools
from collections import deque
from far_check import three_conn


def far(adj):
    Nz = sorted(adj[0])
    H = [set(a) - {0} for a in adj]
    return all(not (v in H[u] or H[u] & H[v]) for u, v in itertools.combinations(Nz, 2))


def all_paths(H, s, t, allowed):
    out = []
    def dfs(p, S):
        v = p[-1]
        for w in sorted(H[v]):
            if w in S:
                continue
            if w == t:
                out.append(p + [t]); continue
            if not allowed(w):
                continue
            S.add(w); dfs(p + [w], S); S.discard(w)
    dfs([s], {s})
    return out


def bfs(H, s, t, allowed, banned):
    seen = {s}; q = deque([s])
    while q:
        v = q.popleft()
        if v == t:
            return True
        for w in H[v]:
            if w in seen or frozenset((v, w)) in banned:
                continue
            if w != t and not allowed(w):
                continue
            seen.add(w); q.append(w)
    return False


def has_chain(H, X, Y, strict):
    x1, x2, x3 = X; y1, y2, y3 = Y
    N2 = H[x2] | {x2}; N3 = H[x3] | {x3}
    for P2 in all_paths(H, y3, x2, lambda w: w not in N3 and w not in (x1, y2, x2)):
        used = {frozenset(e) for e in zip(P2, P2[1:])}
        ban1 = N2 | N3 | {x1} | ({y3} if strict else set())
        if bfs(H, y2, x1, lambda w: w not in ban1, used):
            return True
    return False


def coverage(adj, strict):
    Nz = sorted(adj[0])
    H = [set(a) - {0} for a in adj]
    cov, as_y1 = set(), set()
    for r in Nz:
        rest = [v for v in Nz if v != r]
        found = False
        for x1 in rest:
            four = [v for v in rest if v != x1]
            for a, b, c, d in itertools.permutations(four):
                if has_chain(H, (x1, a, c), (r, b, d), strict):
                    found = True; break
            if found:
                break
        if found:
            cov.add(r); as_y1.add(r); continue
        for perm in itertools.permutations(rest):
            x1, y1, x2, x3, y3 = perm
            if has_chain(H, (x1, x2, x3), (y1, r, y3), strict):
                cov.add(r); break
            x1, y1, x2, y2, x3 = perm
            if has_chain(H, (x1, x2, x3), (y1, y2, r), strict):
                cov.add(r); break
    return cov, as_y1


def ring(k=1, extra_tri=0):
    """six blobs; blob i = triangle v_i a_i b_i; consecutive blobs joined by k disjoint links
    b_i -> a_{i+1} (k = 1) ; z adjacent to all v_i."""
    adj = {}
    def add(u, w):
        adj.setdefault(u, set()).add(w); adj.setdefault(w, set()).add(u)
    z = 0
    V = lambda i: 1 + 3 * i
    A = lambda i: 2 + 3 * i
    Bv = lambda i: 3 + 3 * i
    for i in range(6):
        add(z, V(i)); add(V(i), A(i)); add(V(i), Bv(i)); add(A(i), Bv(i))
        add(Bv(i), A((i + 1) % 6))
    n = 19
    return [adj[v] for v in range(n)]


def priv(rng, extra, dpriv):
    while True:
        n = 19 + extra
        adj = [set() for _ in range(n)]
        def add(u, w):
            adj[u].add(w); adj[w].add(u)
        for i in range(1, 7):
            add(0, i); add(i, 5 + 2 * i); add(i, 6 + 2 * i)
        stubs = [p for p in range(7, 19) for _ in range(dpriv - 1)] + [e for e in range(19, n) for _ in range(3)]
        if len(stubs) % 2:
            return None
        rng.shuffle(stubs)
        ok = True
        for u, w in zip(stubs[::2], stubs[1::2]):
            if u == w or w in adj[u]:
                ok = False; break
            add(u, w)
        if not ok or any(len(adj[v]) % 2 == 0 for v in range(1, n)):
            continue
        if three_conn(n, adj):
            return adj


def main():
    fam = sys.argv[1]
    if fam == 'ring':
        adj = ring()
        n = len(adj)
        print('ring of triangles: order', n, '3-connected', three_conn(n, adj), 'far', far(adj),
              'degrees off z odd', all(len(adj[v]) % 2 for v in range(1, n)))
        for strict in (False, True):
            cov, y1 = coverage(adj, strict)
            print(f'  {"strict (Lean AdmChain)" if strict else "relaxed (Conj 8.5 as stated)"}: covered r {sorted(cov)} of {sorted(adj[0])}; with r = y1: {sorted(y1)}')
        return
    count, seed, extra, dpriv = map(int, sys.argv[2:6])
    rng = random.Random(seed)
    stat = {False: [0, 0], True: [0, 0]}
    made = 0
    while made < count:
        adj = priv(rng, extra, dpriv)
        if adj is None:
            continue
        made += 1
        for strict in (False, True):
            cov, y1 = coverage(adj, strict)
            stat[strict][0] += len(cov) == 6
            stat[strict][1] += len(y1) == 6
    print(f'priv order {19 + extra} dpriv {dpriv}: graphs {made}; relaxed: all r covered {stat[False][0]}, all as y1 {stat[False][1]}; '
          f'strict: all r covered {stat[True][0]}, all as y1 {stat[True][1]}', flush=True)


if __name__ == '__main__':
    main()
