"""Audit A22c: Proposition 8.3 and Theorem 8.2 executed on far-apart instances: the order-19
family of conj19.py (every J up to isomorphism).  For each J and r, take a strict admissible chain
with y1 = r (Definition 8.1 with N = N_G, as in Lean AdmChain), check the hypotheses of
Theorem 3.2 in M exactly as the proof of Prop 8.3 states them, find the separating Lovasz
decomposition (dsolve), and execute the proof of Theorem 8.2 (construct.py) to a verified
decomposition of G.  Also once with the relaxed chain (y3 allowed on P1).
usage: far19_exec.py [step]"""
import sys, itertools, subprocess
from far_check import three_conn, check_sparse_hyp
from conj_check import all_paths, far
from conj19 import partitions, pairings
from count_J import g6_encode, g6_decode
from chain import base_test
import construct
from collections import deque


def bfs_path(H, s, t, allowed, banned):
    prev = {s: None}; q = deque([s])
    while q:
        v = q.popleft()
        if v == t:
            p = [t]
            while prev[p[-1]] is not None:
                p.append(prev[p[-1]])
            return p[::-1]
        for w in sorted(H[v]):
            if w in prev or frozenset((v, w)) in banned:
                continue
            if w != t and not allowed(w):
                continue
            prev[w] = v; q.append(w)
    return None


def chain_for(H, X, Y, strict):
    x1, x2, x3 = X; y1, y2, y3 = Y
    N2 = H[x2] | {x2}; N3 = H[x3] | {x3}
    for P2 in all_paths(H, y3, x2, lambda w: w not in N3 and w not in (x1, y2, x2)):
        used = {frozenset(e) for e in zip(P2, P2[1:])}
        ban1 = N2 | N3 | {x1} | ({y3} if strict else set())
        P1 = bfs_path(H, y2, x1, lambda w: w not in ban1, used)
        if P1:
            return P2, P1
    return None


def main():
    step = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    lines = [l.strip() for l in open('conj19_canon.txt')]
    stat = dict(J=0, chains=0, executed=0, relaxed_with_y3_on_P1=0)
    for s in lines[::step]:
        n, A = g6_decode(s)
        adj = [set(w for w in range(n) if A[u][w]) for u in range(n)]
        z = [v for v in range(n) if len(adj[v]) == 6][0]
        perm = [z] + [v for v in range(n) if v != z]
        inv = {v: i for i, v in enumerate(perm)}
        adj = [set(inv[w] for w in adj[perm[i]]) for i in range(n)]
        # G = (J - z) + F on 0..n-2
        H = [set(w - 1 for w in adj[v] if w != 0) for v in range(1, n)]
        Nz = sorted(v - 1 for v in adj[0])
        stat['J'] += 1
        for r in Nz:
            rest = [v for v in Nz if v != r]
            done = {True: False, False: False}
            for x1 in rest:
                four = [v for v in rest if v != x1]
                for a, b, c, d in itertools.permutations(four):
                    X, Y = (x1, a, c), (r, b, d)
                    for strict in (True, False):
                        if done[strict]:
                            continue
                        ch = chain_for(H, X, Y, strict)
                        if not ch:
                            continue
                        P2, P1 = ch
                        if not strict and Y[2] in P1:
                            stat['relaxed_with_y3_on_P1'] += 1
                        E = {frozenset((u, w)) for u in range(n - 1) for w in H[u]} | {frozenset((X[i], Y[i])) for i in range(3)}
                        check_sparse_hyp(n - 1, E, X, Y, P2, P1)
                        D, _ = base_test(n - 1, E, X, Y, P2, P1)
                        assert D is not None, 'Prop 8.3: no separating decomposition'
                        construct.run(n - 1, E, X, Y, P2, P1, seed=r)
                        stat['chains'] += 1; stat['executed'] += 1
                        done[strict] = True
                    if all(done.values()):
                        break
                if all(done.values()):
                    break
            assert done[True], ('no strict chain', s, r)
    print('far19_exec:', stat, flush=True)


if __name__ == '__main__':
    main()
