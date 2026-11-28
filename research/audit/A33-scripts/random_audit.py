"""Random adversarial tests of nalib.na_construct, checked by my own verifier (indep.verify).

Graphs: disjoint unions of random all-odd pieces plus isolated vertices (the proof's set A contains
odd vertices outside the component of y, so disconnected inputs exercise that branch).  For each
ordered pair x ~ y with the weak hypothesis, and for random packed Y containing x (up to maximal),
the construction is run with both steering methods and verified.  For small orders the iff of
Corollary 1.5 and of the set form is also decided by indep.good.

usage: python3 random_audit.py N TRIALS SEED [--exact]"""
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(1, os.path.abspath(os.path.join(HERE, "..", "..", "..", "manuscripts", "na", "scripts")))
import indep  # noqa: E402
import nalib  # noqa: E402

N, TRIALS, SEED = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
EXACT = "--exact" in sys.argv
rng = random.Random(SEED)
S = dict(graphs=0, pairs=0, weak=0, built=0, fail=0, sets=0, sets_weak=0, sets_fail=0,
         iff_checked=0, iff_fail=0, set_iff_checked=0, set_iff_fail=0)


def random_allodd(vs, p):
    G = {v: set() for v in vs}
    for i, a in enumerate(vs):
        for b in vs[i + 1:]:
            if rng.random() < p:
                G[a].add(b)
                G[b].add(a)
    ev = [v for v in vs if len(G[v]) % 2 == 0]
    rng.shuffle(ev)
    if len(ev) % 2:
        return None
    for i in range(0, len(ev), 2):
        a, b = ev[i], ev[i + 1]
        if b in G[a]:
            G[a].discard(b)
            G[b].discard(a)
        else:
            G[a].add(b)
            G[b].add(a)
    return G


for _ in range(TRIALS):
    # two pieces + up to two isolated vertices
    n1 = rng.randrange(2, N - 1)
    n1 -= n1 % 2
    n2 = (N - n1) - (N - n1) % 2
    vs = list(range(N))
    rng.shuffle(vs)
    G = {v: set() for v in vs}
    ok = True
    for piece in (vs[:n1], vs[n1:n1 + n2]):
        if len(piece) < 2:
            continue
        H = random_allodd(piece, rng.uniform(0.2, 0.8))
        if H is None:
            ok = False
            break
        for v in H:
            G[v] |= H[v]
    if not ok or any(len(G[v]) % 2 == 0 and len(G[v]) > 0 for v in G):
        continue
    S["graphs"] += 1
    for y in G:
        for x in sorted(G[y]):
            S["pairs"] += 1
            wk = indep.weak(G, y, {x})
            if EXACT and N <= 10:
                S["iff_checked"] += 1
                if indep.good(G, y, {x}) != wk:
                    S["iff_fail"] += 1
                    print("IFF FAIL", G, y, x)
            if not wk:
                continue
            S["weak"] += 1
            for method in ("paper", "tjoin"):
                D, W = nalib.na_construct(G, y, {x}, method)
                S["built"] += 1
                good, msg = indep.verify(G, D, y, {x})
                if not good:
                    S["fail"] += 1
                    print("FAIL", method, G, y, x, msg)
            # random packed Y containing x
            Y = {x}
            cand = [v for v in G if v != y and v != x]
            rng.shuffle(cand)
            for v in cand:
                if rng.random() < 0.7 and indep.packed(G, Y | {v}):
                    Y.add(v)
            if len(Y) == 1:
                continue
            S["sets"] += 1
            wks = indep.weak(G, y, Y)
            if EXACT and N <= 10:
                S["set_iff_checked"] += 1
                if indep.good(G, y, Y, meets_once=True) != wks:
                    S["set_iff_fail"] += 1
                    print("SET IFF FAIL", G, y, Y)
            if wks:
                S["sets_weak"] += 1
                D, W = nalib.na_construct(G, y, Y)
                good, msg = indep.verify(G, D, y, Y)
                if not good:
                    S["sets_fail"] += 1
                    print("SET FAIL", G, y, Y, msg)
print("N=%d seed=%d " % (N, SEED) + " ".join("%s=%d" % kv for kv in S.items()), flush=True)
