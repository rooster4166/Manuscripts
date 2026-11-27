"""A16: run the proof of Theorem 19 (separation), Theorem 21 (L1, leaf trick), Corollary 20 and
Corollary 22 of route-descent.tex as algorithms, and check every output independently.

sep(K, X) follows the induction of Theorem 19 literally (Cases I-IV), with random choices
wherever the proof says "choose any". Lemma 3 is a16_core.fan, which asserts its own conclusions.
Every recursive call asserts the invariants the proof claims (at most one positive-even vertex,
X packed, nu decreasing, the end counts stated in each case, Z = empty where claimed).

Modes:
  sep    random K with <= 1 positive-even vertex, random packed X       (Theorem 19)
  l1     random all-odd F, c, packed Y outside N[c]; leaf trick          (Theorem 21)
  pair   X = {c, a} at distance >= 3                                    (Theorem 19, pair form)
  onepair  G with exactly two even vertices a ~ c                        (Corollary 22)
  dist2  X independent but NOT packed: where does the proof break?

Usage: python3 a16_sep_test.py MODE [trials] [seed]
"""
import random
import sys

import a16_core as C


class ProofFail(Exception):
    pass


STATS = {}


def bump(k):
    STATS[k] = STATS.get(k, 0) + 1


def nu(adj):
    return 2 * len(C.edges(adj)) + (0 if C.even_set(adj) else 1)


_fresh = [0]


def fresh():
    _fresh[0] += 1
    return ("leaf", _fresh[0])


def sep(K, X, rng, require_packed=True):
    ev = C.even_set(K)
    assert len(ev) <= 1, "more than one positive-even vertex"
    if require_packed:
        assert C.packed(K, X), "X not packed"
    X = set(X)
    if ev:  # Case I
        z = ev[0]
        cand = sorted((u for u in K[z] if u not in X), key=str)
        if not cand:
            raise ProofFail(("I", z, z in X, sorted(K[z], key=str)))
        u = rng.choice(cand)
        assert len(K[u]) % 2 == 1, "u not odd"
        K1 = C.copy(K)
        C.del_edge(K1, u, z)
        assert len(C.even_set(K1)) <= 1 and nu(K1) < nu(K)
        D1 = sep(K1, X, rng, require_packed)
        b = C.ends_count(D1, K1)
        assert b[z] == 1 and b[u] == 0
        assert C.Zset(K1, D1, u) == set(), "Z(u) nonempty in Case I"
        _, D, _ = C.fan(K1, D1, z, u)
        bump("I")
        return D
    big = sorted((x for x in K if x not in X and len(K[x]) >= 3), key=str)
    if big:  # Case II
        x = rng.choice(big)
        u = rng.choice(sorted(K[x], key=str))
        H = C.copy(K)
        C.del_edge(H, u, x)
        ell = fresh()
        H[ell] = set()
        C.add_edge(H, u, ell)
        assert C.even_set(H) == [x] and nu(H) < nu(K)
        DH = sep(H, X, rng, require_packed)
        qs = [i for i, P in enumerate(DH) if ell in P]
        assert len(qs) == 1
        P = DH[qs[0]]
        assert ell in (P[0], P[-1]), "leaf not an end"
        if P[0] != ell:
            P = P[::-1]
        D1 = [Q for j, Q in enumerate(DH) if j != qs[0]]
        if len(P) == 2:
            bump("II-single")
        else:
            D1.append(P[1:])
        K1 = C.copy(K)
        C.del_edge(K1, u, x)
        b = C.check_partition(K1, D1)
        assert C.meets_once(D1, X)
        assert b[x] == 0 and b[u] in (0, 2)
        for w in K1:
            if w not in (u, x):
                assert b[w] == len(K[w]) % 2
        if b[u] == 0:
            D = D1 + [[u, x]]
            bump("II-b0")
        else:
            assert C.Zset(K1, D1, x) == set(), "Z(x) nonempty in Case II"
            _, D, _ = C.fan(K1, D1, u, x)
            bump("II-b2")
        return D
    small = sorted((v for v in K if v not in X and K[v]), key=str)
    if small:  # Case III
        v = rng.choice(small)
        assert len(K[v]) == 1
        (w,) = tuple(K[v])
        K1 = C.copy(K)
        C.del_edge(K1, v, w)
        assert nu(K1) < nu(K)
        D1 = sep(K1, X, rng, require_packed)
        b = C.ends_count(D1, K1)
        assert b[w] == 0 and b[v] == 0
        bump("III")
        return D1 + [[v, w]]
    # Case IV
    if C.edges(K):
        raise ProofFail(("IV", sorted(map(lambda e: tuple(sorted(e, key=str)), C.edges(K)))))
    bump("IV")
    return []


def check_sep(K, X, D):
    C.check_partition(K, D, C.lovasz_profile(K))
    assert C.meets_once(D, X), "a path meets X twice"


def random_packed(K, rng, maxsize=None, avoid=()):
    V = [v for v in K if v not in avoid]
    rng.shuffle(V)
    X = []
    for v in V:
        if all(C.dist(K, v, x) >= 3 for x in X):
            X.append(v)
            if maxsize and len(X) >= maxsize:
                break
    return X


def random_independent_not_packed(K, rng):
    V = list(K)
    rng.shuffle(V)
    X = []
    for v in V:
        if all(x not in K[v] and x != v for x in X):
            X.append(v)
    return X if not C.packed(K, X) else None


def leaf_trick(F, c, Y, rng):
    """Theorem 21: K = F + c ell, X = Y + {ell}; separate; delete ell."""
    K = C.copy(F)
    ell = fresh()
    K[ell] = {c}
    K[c].add(ell)
    assert C.even_set(K) == [c]
    X = set(Y) | {ell}
    assert C.packed(K, X)
    DK = sep(K, X, rng)
    check_sep(K, X, DK)
    (i,) = [j for j, P in enumerate(DK) if ell in P]
    P = DK[i] if DK[i][0] == ell else DK[i][::-1]
    assert P[0] == ell and P[1] == c and len(P) >= 3
    D = [Q for j, Q in enumerate(DK) if j != i] + [P[1:]]
    C.check_partition(F, D, C.lovasz_profile(F))
    Qc = [Q for Q in D if c in (Q[0], Q[-1])]
    assert len(Qc) == 1
    assert not (set(Qc[0]) & set(Y)), "Q_c meets Y"
    assert C.meets_once(D, Y)
    return D


def main():
    mode = sys.argv[1]
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 500
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    rng = random.Random(seed)
    done = 0
    fails = {}
    for _ in range(trials):
        n = rng.randint(3, 14)
        p = rng.uniform(0.1, 0.6)
        if mode in ("sep", "pair", "dist2"):
            K = C.random_one_even(n, p, rng)
            if not C.edges(K):
                continue
            if mode == "sep":
                X = random_packed(K, rng)
            elif mode == "pair":
                V = list(K)
                prs = [(x, y) for x in V for y in V if x != y and C.dist(K, x, y) >= 3]
                if not prs:
                    continue
                X = list(rng.choice(prs))
            else:
                X = random_independent_not_packed(K, rng)
                if X is None:
                    continue
            if mode == "dist2":
                try:
                    D = sep(K, X, rng, require_packed=False)
                    check_sep(K, X, D)
                    fails["succeeded anyway"] = fails.get("succeeded anyway", 0) + 1
                except ProofFail as e:
                    kind = e.args[0][0]
                    detail = "Case I: even z has all neighbours in X" if kind == "I" else "Case IV"
                    if kind == "I" and e.args[0][2]:
                        detail += " (z in X)"
                    fails[detail] = fails.get(detail, 0) + 1
                done += 1
                continue
            D = sep(K, X, rng)
            check_sep(K, X, D)
            done += 1
        elif mode == "l1":
            F = C.make_odd(C.random_graph(n, p, rng), rng)
            cs = [v for v in F if F[v]]
            if not cs:
                continue
            c = rng.choice(cs)
            Y = random_packed(F, rng, maxsize=rng.randint(1, 4), avoid=set(F[c]) | {c})
            if not Y:
                continue
            leaf_trick(F, c, Y, rng)
            done += 1
        elif mode == "onepair":
            F = C.make_odd(C.random_graph(n, p, rng), rng)
            V = [v for v in F if F[v]]
            prs = [(c, a) for c in V for a in V if c != a and a not in F[c]]
            if not prs:
                continue
            c, a = rng.choice(prs)
            G = C.copy(F)
            C.add_edge(G, c, a)
            assert sorted(C.even_set(G), key=str) == sorted([a, c], key=str)
            D = leaf_trick(F, c, [a], rng)
            (Qc,) = [Q for Q in D if c in (Q[0], Q[-1])]
            Qc = Qc if Qc[-1] == c else Qc[::-1]
            newP = Qc + [a]  # append the route c a at the tail c (Proposition 15)
            DG = [Q for Q in D if Q is not Qc and Q != Qc[::-1]] + [newP]
            b = {v: (len(G[v]) % 2) for v in G}
            b[a] = 2
            b[c] = 0
            C.check_partition(G, DG, b)
            assert newP[-1] == a and newP[-2] == c, "ca not terminal at a"
            done += 1
        else:
            raise SystemExit("unknown mode")
    what = "instances run (outcomes below)" if mode == "dist2" else "instances, all outputs checked"
    print(f"mode {mode}: {done} {what}; case counts {dict(sorted(STATS.items()))}")
    if fails:
        print("dist2 outcomes:", fails)
    print("Lemma 3 calls:", C.FAN_STATS.calls, "chain lengths", dict(sorted(C.FAN_STATS.chain_len.items())))


if __name__ == "__main__":
    main()
