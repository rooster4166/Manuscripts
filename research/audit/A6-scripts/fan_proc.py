"""Test Fan's Lemma 3.3 (grouped addible edge) by running Fan's own sequence
construction on random decompositions, validating every output, and, when the
construction finds nothing, checking existence exactly with CP-SAT."""
import random, sys, itertools
from common import *
from fan_test import random_decomp, ends
def fan_transfer(G, D, a, X):
    """Return new decomposition of G + {x a} for some x in X, or None."""
    b = ends(D, G.nodes())
    edge_owner = {}
    for i, P in enumerate(D):
        for u, w in zip(P, P[1:]): edge_owner[frozenset((u, w))] = i
    for x in X:
        for i0, P0 in enumerate(D):
            if b[x] == 0 or x not in (P0[0], P0[-1]): continue
            starts = [j for j in (0, len(P0) - 1) if P0[j] == x]
            for _ in starts:
                seq = []  # list of (b_i, path index)
                bi, pi = x, i0
                visited_b = set()
                ok = None
                while True:
                    if bi in visited_b: ok = None; break
                    visited_b.add(bi)
                    P = D[pi]
                    seq.append((bi, pi))
                    if a not in P:
                        ok = True; break
                    # orient P from bi
                    Q = list(P) if P[0] == bi else list(P)[::-1]
                    assert Q[0] == bi
                    j = Q.index(a)
                    nb = Q[j - 1]
                    if b[nb] == 0: ok = False; break
                    # choose a path with end nb (prefer one not used yet)
                    cand = [k for k, R in enumerate(D) if nb in (R[0], R[-1])]
                    pi = cand[0]; bi = nb
                if not ok: continue
                # apply modifications on edge sets
                Es = [set(frozenset(e) for e in zip(P, P[1:])) for P in D]
                for t, (bi, pi) in enumerate(seq):
                    if t < len(seq) - 1:
                        nbv = seq[t + 1][0]
                        Es[pi].discard(frozenset((nbv, a)))
                    Es[pi].add(frozenset((bi, a)))
                newD = []
                good = True
                for Eset in Es:
                    H = nx.Graph([tuple(e) for e in Eset])
                    if H.number_of_edges() == 0: good = False; break
                    if not (nx.is_connected(H) and max(dict(H.degree()).values()) <= 2 and H.number_of_edges() == H.number_of_nodes() - 1):
                        good = False; break
                    e2 = [v for v in H if H.degree(v) == 1]
                    newD.append(tuple(nx.shortest_path(H, e2[0], e2[1])))
                if not good: continue
                G2 = G.copy(); G2.add_edge(x, a)
                if not verify_partition(G2, newD): continue
                nb2 = ends(newD, G2.nodes())
                want = dict(b); want[x] -= 1; want[a] += 1
                if nb2 == want and len(newD) == len(D):
                    return x, newD
    return None
def trial(seed):
    rng = random.Random(seed)
    n = rng.randint(5, 11)
    G = nx.gnp_random_graph(n, rng.uniform(0.25, 0.85), seed=rng.randint(0, 10**9))
    if G.number_of_edges() < 3: return None
    D = random_decomp(G, rng)
    b = ends(D, G.nodes())
    a = rng.choice(list(G.nodes()))
    non = [u for u in G.nodes() if u != a and not G.has_edge(u, a)]
    if not non: return None
    X = rng.sample(non, rng.randint(1, min(len(non), 5)))
    Z = sum(1 for w in G.neighbors(a) if b[w] == 0)
    if not sum(b[u] for u in X) > Z: return None
    r = fan_transfer(G, D, a, X)
    if r is not None: return ('constructed', len(X))
    # fallback: exact check
    for u in X:
        if b[u] == 0: continue
        G2 = G.copy(); G2.add_edge(u, a)
        want = dict(b); want[u] -= 1; want[a] += 1
        res = solve(G2, exact_ends=want, workers=1, time_limit=120)
        if res.status in ('OPTIMAL', 'FEASIBLE'): return ('exists-but-construction-missed', len(X))
    return ('LEMMA-FAILS', seed)
if __name__ == '__main__':
    from collections import Counter
    c = Counter(); N = int(sys.argv[1]); s = int(sys.argv[2]); done = 0; bad = []
    while done < N:
        r = trial(s); s += 1
        if r is None: continue
        done += 1; c[(r[0], r[1] if r[0] != 'LEMMA-FAILS' else 0)] += 1
        if r[0] != 'constructed': bad.append((r, s - 1))
    print(sorted(c.items())); print(bad[:5])
