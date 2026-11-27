"""exp1.py: one step of Lovasz's induction for DL(1) (session claude/dl-one).

For every core instance (G, a, b): G has one even vertex g, a, b in N(g) odd, ab not an edge,
not universal twins.  For every target u in N(g): enumerate all Lovasz decompositions D' of
G - gu, apply the forced Fan transfer g -> u, and record
  ex(u)  : some D' transfers to a DL-good decomposition of G;
  rob(u) : (u not in {a,b}) every D' that is DL-good for (a,b) in G - gu transfers to a good one.
usage: exp1.py FILE.g6 [cap]
"""
import sys
from collections import Counter
import dllib

def main():
    cap = int(sys.argv[2]) if len(sys.argv) > 2 else 100000
    C = Counter()
    for line in open(sys.argv[1]):
        g6 = line.strip()
        if not g6:
            continue
        n, E = dllib.g6_decode(g6)
        ev = dllib.even_vertices(n, E)
        if len(ev) != 1:
            continue
        g = ev[0]
        A = dllib.adjsets(n, E)
        d = dllib.degrees(n, E)
        Nb = sorted(A[g])
        pairs = [(a, b) for a in Nb for b in Nb if a < b and d[a] % 2 and d[b] % 2 and b not in A[a]
                 and not dllib.univ_twins(n, E, a, b)]
        if not pairs:
            continue
        cache = {}
        for u in Nb:
            K = dllib.remove_edge(E, g, u)
            Ds, comp = dllib.enum_decomps(n, K, cap)
            if not comp:
                cache[u] = None
                continue
            res = []
            for Dp in Ds:
                D, chain = dllib.fan_transfer(Dp, g, u)
                assert dllib.is_lovasz(n, E, D), (g6, u, Dp, D)
                res.append((Dp, D, chain))
            cache[u] = res
        for a, b in pairs:
            C["inst"] += 1
            exs, robs = [], []
            undec = False
            for u in Nb:
                res = cache[u]
                if res is None:
                    undec = True
                    continue
                ex = any(dllib.dl_good(D, a, b) for Dp, D, ch in res)
                if ex:
                    exs.append(u)
                if u not in (a, b):
                    kids = [(Dp, D) for Dp, D, ch in res if dllib.dl_good(Dp, a, b)]
                    if kids and all(dllib.dl_good(D, a, b) for Dp, D in kids):
                        robs.append(u)
            if undec:
                C["undec"] += 1
            if not exs:
                C["NO_EXISTENTIAL_TARGET"] += 1
                print("NOEX", g6, "g=%d a=%d b=%d" % (g, a, b), flush=True)
            if robs:
                C["robust_target"] += 1
            else:
                C["no_robust"] += 1
                kinds = []
                for u in Nb:
                    kinds.append("%d:%s%s" % (u, "a" if u == a else "b" if u == b else
                                           ("A" if u in A[a] else "") + ("B" if u in A[b] else "") or "-",
                                           "+" if u in exs else ""))
                print("NOROB", g6, "g=%d a=%d b=%d" % (g, a, b), "targets", " ".join(kinds),
                      "cn", sorted(A[a] & A[b]), flush=True)
            if a in exs or b in exs:
                C["ab_target_ex"] += 1
    print(dict(C))

main()
