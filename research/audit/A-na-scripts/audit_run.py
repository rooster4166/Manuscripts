"""Audit driver for manuscripts/na.

usage: nauty-geng -cq N | python3 -B audit_run.py [--sets] [--lds] [--limit K] [--every M]

For every connected graph with all degrees odd and every ordered pair (y, x), x ~ y:
  * my own exact solver (indep.good) decides whether Q(y) can avoid x; compare with the weak
    hypothesis (Corollary 1.5) and with exact.avoid_exact of the manuscript;
  * run nalib.na_construct with both steering methods on the weak pairs, and check each output
    with my own verifier (indep.verify);
  * instrument the construction: at every Fan back-step record b(t) and |Z(u)| (Lemma 3.2 claims
    b(t) = 1 and Z(u) empty), check Definition 3.1 and Lemma 3.3(1) on the steering sequence, and the
    hypotheses of L1 at the bottom of the chain; count how often the target is y itself;
  * --lds: enumerate all Lovasz decompositions (indep.all_lovasz) and check the per-path identity
    e(P) = n(P) of Section 6 for paths through x on the non-weak pairs, and x in Q(y);
  * --sets: every packed Y containing x with |Y| <= 3: the set-form iff (avoid_packed_iff_reach),
    decided by my solver with meets_once, and the construction checked by my verifier.
"""
import os
import sys
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
SCRIPTS = os.path.join(HERE, "..", "..", "..", "manuscripts", "na", "scripts")
sys.path.insert(0, HERE)
sys.path.insert(1, os.path.abspath(SCRIPTS))

import indep  # noqa: E402
import nalib  # noqa: E402
import exact  # noqa: E402

args = sys.argv[1:]
LIMIT = int(args[args.index("--limit") + 1]) if "--limit" in args else None
EVERY = int(args[args.index("--every") + 1]) if "--every" in args else 1

# ------------------------------------------------------------------ instrumentation of Fan
fan_log = []
_orig_fan = nalib.fan


def fan_logged(K, D, t, u):
    b = nalib.ends_count(D)
    Z = [w for w in K.get(u, ()) if b.get(w, 0) == 0]
    fan_log.append((b.get(t, 0), len(Z)))
    return _orig_fan(K, D, t, u)


nalib.fan = fan_logged

# l1 at the bottom of the chain: record hypotheses
l1_log = []
_orig_l1 = nalib.l1


def l1_logged(F, c, Y):
    l1_log.append((indep.packed(F, Y), c not in Y and not (F[c] & set(Y)),
                   all(len(F[v]) % 2 == 1 or len(F[v]) == 0 for v in F), len(F[c]) % 2 == 1))
    return _orig_l1(F, c, Y)


nalib.l1 = l1_logged

S = dict(graphs=0, pairs=0, na=0, weak=0, good=0, iff_fail=0, exact_disagree=0, built=0,
         verify_fail=0, fan_steps=0, fan_bad=0, l1_bad=0, steer_bad=0, target_y=0,
         seq_with_y_target=0, lds_checked=0, identity_fail=0, sets=0, sets_iff_fail=0,
         sets_built=0, sets_verify_fail=0)


def check_steer(G, y, Y, l, W):
    """Definition 3.1 and Lemma 3.3(1) for W in K = G + y l, X = Y + {l}."""
    K = {v: set(N) for v, N in G.items()}
    K[y].add(l)
    K[l] = {y}
    X = set(Y) | {l}
    es = [frozenset(p) for p in zip(W, W[1:])]
    if len(set(es)) != len(es) or len(W) < 2 or W[0] != y:
        return False
    if any(g in X for g in W[1:]):
        return False
    for a, b in zip(W, W[1:]):
        if b not in K[a]:
            return False
    Ki = {v: set(N) for v, N in K.items()}
    for i in range(len(W) - 1):
        ev = [v for v in Ki if len(Ki[v]) > 0 and len(Ki[v]) % 2 == 0]
        if ev != [W[i]]:
            return False
        Ki[W[i]].discard(W[i + 1])
        Ki[W[i + 1]].discard(W[i])
        # no edge at X deleted
        if W[i] in X or W[i + 1] in X:
            return False
    ev = [v for v in Ki if len(Ki[v]) > 0 and len(Ki[v]) % 2 == 0]
    if ev or len(Ki[W[-1]]) != 0:
        return False
    if Ki[l] != {y}:
        return False
    return True


count = 0
for line in sys.stdin:
    if not line.strip():
        continue
    count += 1
    if (count - 1) % EVERY:
        continue
    G = indep.read_g6(line)
    if any(len(G[v]) % 2 == 0 for v in G):
        continue
    S["graphs"] += 1
    if LIMIT and S["graphs"] > LIMIT:
        break
    exact.decomposable.cache_clear()
    lds = indep.all_lovasz(G) if "--lds" in args else None
    for y in G:
        for x in sorted(G[y]):
            S["pairs"] += 1
            na = any(w != x and w not in G[x] for w in G[y])
            wk = indep.weak(G, y, {x})
            S["na"] += na
            S["weak"] += wk
            gd = indep.good(G, y, {x})
            S["good"] += gd
            if gd != wk:
                S["iff_fail"] += 1
                print("IFF FAIL", line.strip(), y, x, gd, wk, flush=True)
            if (exact.avoid_exact(G, y, {x}) is not None) != gd:
                S["exact_disagree"] += 1
                print("EXACT DISAGREES", line.strip(), y, x, flush=True)
            if lds is not None and not wk:
                for D in lds:
                    S["lds_checked"] += 1
                    Q = [P for P in D if y in (P[0], P[-1])][0]
                    if x not in Q:
                        S["identity_fail"] += 1
                    C = indep.component(G, y, {x})
                    for P in D:
                        n = (P[0] in C) + (P[-1] in C)
                        e = sum(1 for a, b in zip(P, P[1:]) if (a == x and b in C) or (b == x and a in C))
                        if (x in P and e != n) or e > n:
                            S["identity_fail"] += 1
            if wk:
                for method in ("paper", "tjoin"):
                    fan_log.clear()
                    l1_log.clear()
                    D, W = nalib.na_construct(G, y, {x}, method)
                    S["built"] += 1
                    ok, msg = indep.verify(G, D, y, {x})
                    if not ok:
                        S["verify_fail"] += 1
                        print("VERIFY FAIL", method, line.strip(), y, x, msg, flush=True)
                    if W is not None:
                        # the leaf vertex used: the one not in G adjacent to y in the chain? rebuild
                        l = ("audit-leaf",)
                        if not check_steer(G, y, {x}, l, W):
                            S["steer_bad"] += 1
                            print("STEER BAD", method, line.strip(), y, x, W, flush=True)
                        ny = sum(1 for g in W[1:] if g == y)
                        S["target_y"] += ny
                        S["seq_with_y_target"] += (ny > 0)
                    for bt, z in fan_log:
                        S["fan_steps"] += 1
                        if not (bt == 1 and z == 0):
                            S["fan_bad"] += 1
                    for rec in l1_log:
                        if not all(rec):
                            S["l1_bad"] += 1
            if "--sets" in args:
                others = [v for v in G if v not in (x, y) and v not in G[y]]
                for r in (1, 2):
                    for extra in combinations(others, r):
                        Y = {x, *extra}
                        if not indep.packed(G, Y):
                            continue
                        S["sets"] += 1
                        wks = indep.weak(G, y, Y)
                        gds = indep.good(G, y, Y, meets_once=True)
                        if wks != gds:
                            S["sets_iff_fail"] += 1
                            print("SET IFF FAIL", line.strip(), y, Y, gds, wks, flush=True)
                        if wks:
                            D, W = nalib.na_construct(G, y, Y)
                            S["sets_built"] += 1
                            ok, msg = indep.verify(G, D, y, Y)
                            if not ok:
                                S["sets_verify_fail"] += 1
                                print("SET VERIFY FAIL", line.strip(), y, Y, msg, flush=True)

print(" ".join("%s=%d" % kv for kv in S.items()), flush=True)
