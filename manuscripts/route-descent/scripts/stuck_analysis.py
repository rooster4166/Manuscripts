"""Analyse stuck instances of the extension step (no pair p admits the extension).

For each stuck (G, P, M) from outputs/stuck_*.jsonl:
  * for each route R_p: is the failure *trivial*, i.e. N_{G'}(c) is contained in V(R_p), so that
    the path at c cannot even leave R_p?  (`triv`)
  * re-routing: sample random Theorem-21 constructions of G; keep those whose pairing equals P;
    does some kept construction admit the extension for some p (with the same M)?

Usage: python3 stuck_analysis.py FILE [samples]
"""
import json
import random
import sys

import networkx as nx

import rd_lib as L


def ext_vector(G, routes, M):
    Mset = set(M)
    out = []
    for R in routes:
        a, c = (R[0], R[-1]) if R[0] in Mset else (R[-1], R[0])
        G2 = L.delete_route(G, R)
        b2 = L.simple_profile(G2, Mset - {a})
        out.append(L.ext(G2, b2, c, set(R) - {c}))
    return out


def trivial(G, R, M):
    a, c = (R[0], R[-1]) if R[0] in set(M) else (R[-1], R[0])
    G2 = L.delete_route(G, R)
    return set(G2[c]) <= set(R)


def main():
    fn = sys.argv[1]
    samples = int(sys.argv[2]) if len(sys.argv) > 2 else 400
    rng = random.Random(11)
    tot = triv_all = fixed = nofix = 0
    for line in open(fn):
        d = json.loads(line)
        n = 1 + max(max(e) for e in d["edges"])
        G = nx.Graph()
        G.add_nodes_from(range(n))
        G.add_edges_from(map(tuple, d["edges"]))
        P = {frozenset((r[0], r[-1])) for r in d["routes"]}
        M = d["M"]
        tot += 1
        tv = [trivial(G, R, M) for R in d["routes"]]
        triv_all += all(tv)
        found = None
        same = 0
        for _ in range(samples):
            pairs, routes, links = L.random_construction(G, rng)
            if {frozenset(p) for p in pairs} != P:
                continue
            same += 1
            ev = ext_vector(G, routes, M)
            if any(ev):
                found = routes
                break
        if found:
            fixed += 1
        else:
            nofix += 1
        degc = [G.degree(R[0] if R[-1] in set(M) else R[-1]) for R in d["routes"]]
        print(d["g"], "routes", d["routes"], "M", M, "trivial", tv, "deg c", degc,
              "| same-P constructions tried", same, "| rerouted fix:", found)
    print(f"{tot} stuck; all routes trivially obstructed in {triv_all}; fixed by re-routing {fixed}; not fixed {nofix}")


if __name__ == "__main__":
    main()
