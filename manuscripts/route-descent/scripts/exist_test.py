"""Existential version of the extension step (task C).

For a Thm-21 system (G, P, R) and an even root r, the one-step existential induction closes at
(G, P, r) iff there are a transversal M containing r and a pair p with ext(M, p): realise M - a_p
in G - E(R_p) with the path at c_p avoiding R_p - c_p.  (For p containing r the marked end is r;
for other p either orientation may be chosen, since M ranges over all transversals containing r.)

Reports, per family: universal failures (transversals M with no p), existential failures (roots r
with no (M, p)), with tree T-joins (where the universal step can fail).

Usage: python3 exist_test.py n count constructions [pmin pmax]
"""
import random
import sys

import families
import rd_lib as L


def main():
    n, count, ncons = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    pmin = float(sys.argv[4]) if len(sys.argv) > 4 else 0.15
    pmax = float(sys.argv[5]) if len(sys.argv) > 5 else 0.35
    rng = random.Random(99)
    uni_fail = uni_tot = ex_fail = ex_tot = 0
    ex_fail_list = []
    for G in families.random_graphs(n, count, 1000 + n, pmin, pmax):
        for _ in range(ncons):
            pairs, routes, links = L.random_construction(G, rng, "tree")
            good = {}
            for M in L.transversals(pairs):
                Mset = set(M)
                ok = False
                for R in routes:
                    a, c = (R[0], R[-1]) if R[0] in Mset else (R[-1], R[0])
                    G2 = L.delete_route(G, R)
                    if L.ext(G2, L.simple_profile(G2, Mset - {a}), c, set(R) - {c}):
                        ok = True
                        break
                good[M] = ok
                uni_tot += 1
                uni_fail += not ok
            for r in L.even_vertices(G):
                ex_tot += 1
                if not any(ok for M, ok in good.items() if r in M):
                    ex_fail += 1
                    ex_fail_list.append((sorted(G.edges()), routes, r))
    print(f"n={n}: universal step fails at {uni_fail}/{uni_tot} transversals; "
          f"existential step fails at {ex_fail}/{ex_tot} roots")
    for x in ex_fail_list[:5]:
        print("  ex-fail", x)


if __name__ == "__main__":
    main()
