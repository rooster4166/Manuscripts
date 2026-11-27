"""Test TRC and measure the route-descent extension step.

For each graph G and each of several random Theorem-21 constructions (pairing P with routes R_p and
linking paths), and for every transversal M of P (or a random sample when there are too many):

  * TRC: is b_M realisable?  (A failure is a counterexample to TRC.)
  * extension step: for each pair p = {a, c} with a in M, put G' = G - E(R_p) and
    b' = b_{M - a} on G'; is there a realisation of b' in G' whose path at c avoids V(R_p) - c?
    ext(M, p) = that.  close(M) = exists p with ext(M, p).
  * heredity (Observation 2) is asserted for every route: J - R_p is a forest T-join for
    Ev(G') = Ev - {a, c}, F' = F, and the linking paths of the remaining transitions pair the odd
    vertices of every F'^v by edge-disjoint paths of F'^v.

Usage: python3 trc_test.py FAMILY [constructions] [max_transversals] [seed]
  FAMILY in: order12, g18, g2half, g2full, gbad, rand10, rand12, rand14
"""
import json
import os
import random
import sys
import time

import networkx as nx

import families
import rd_lib as L

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "outputs")


def check_heredity(G, routes, links, i):
    R = routes[i]
    a, c = R[0], R[-1]
    J = {frozenset(e) for r in routes for e in zip(r, r[1:])}
    ER = {frozenset(e) for e in zip(R, R[1:])}
    G2 = L.delete_route(G, R)
    J2 = J - ER
    Ev, Ev2 = set(L.even_vertices(G)), set(L.even_vertices(G2))
    assert Ev2 == Ev - {a, c}, "Ev(G') != Ev - {a,c}"
    dJ2 = {v: 0 for v in G}
    for e in J2:
        for x in e:
            dJ2[x] += 1
    assert {v for v in G if dJ2[v] % 2} == Ev2, "J' is not a T-join for Ev(G')"
    assert all(G2.degree(v) > 0 for v in G2), "isolated vertex in G'"
    for comp in nx.connected_components(G2):
        assert len(comp) % 2 == 0, "odd component"
    F = nx.Graph([e for e in G.edges() if frozenset(e) not in J])
    F.add_nodes_from(G)
    F2 = nx.Graph([e for e in G2.edges() if frozenset(e) not in J2])
    F2.add_nodes_from(G)
    assert {frozenset(e) for e in F.edges()} == {frozenset(e) for e in F2.edges()}, "F' != F"
    pos = {v: j for j, v in enumerate(R)}
    for v, pr in links.items():
        # the transition of R at v
        drop = None
        if v in pos:
            j = pos[v]
            if 0 < j < len(R) - 1:
                drop = frozenset((R[j - 1], R[j + 1]))
            elif j == 0:
                drop = frozenset((R[1], v))
            else:
                drop = frozenset((R[-2], v))
        rest = [(x, y, P) for x, y, P in pr if frozenset((x, y)) != drop]
        assert len(rest) == len(pr) - (drop is not None)
        Fv2 = L.free_graph_at(G2, F2, v)
        odd = {x for x in Fv2 if Fv2.degree(x) % 2}
        ends = [x for x, y, _ in rest] + [y for x, y, _ in rest]
        assert sorted(ends) == sorted(odd), "remaining links do not pair the odd vertices of F'^v"
        used = set()
        for x, y, P in rest:
            for e in zip(P, P[1:]):
                f = frozenset(e)
                assert Fv2.has_edge(*e) and f not in used, "link not in F'^v or not edge-disjoint"
                used.add(f)
    return True


def run(name, graphs, ncons, maxT, seed):
    rng = random.Random(seed)
    t0 = time.time()
    stats = dict(graphs=0, constructions=0, transversals=0, trc_fail=0, ext_queries=0, ext_true=0,
                 close=0, stuck=0, all_p=0)
    stuck_log = []
    nontriv_log = []
    rr_log = []
    hist = {}
    for gname, G in graphs:
        stats["graphs"] += 1
        Ev = L.even_vertices(G)
        if len(Ev) < 2:
            continue
        for _ in range(ncons):
            pairs, routes, links = L.random_construction(G, rng, os.environ.get("TJOIN", "tree"))
            stats["constructions"] += 1
            for i in range(len(routes)):
                check_heredity(G, routes, links, i)
            Ts = list(L.transversals(pairs)) if 2 ** len(pairs) <= maxT else \
                [tuple(p[rng.randrange(2)] for p in pairs) for _ in range(maxT)]
            for M in Ts:
                stats["transversals"] += 1
                b = L.simple_profile(G, M)
                rr_w = None
                if os.environ.get("RR"):
                    rr_w = L.route_respecting(G, routes, M, want=True)
                rb = True if rr_w is not None else L.realisable(G, b)
                if rb is None:
                    stats["unknown_real"] = stats.get("unknown_real", 0) + 1
                    continue
                if not rb:
                    stats["trc_fail"] += 1
                    print("TRC FAILURE", gname, sorted(G.edges()), "routes", routes, "M", M, flush=True)
                    with open(os.path.join(OUT, "TRC_FAILURE.txt"), "a") as f:
                        f.write(json.dumps(dict(g=gname, edges=sorted(G.edges()), routes=routes, M=M)) + "\n")
                    continue
                Mset = set(M)
                if os.environ.get("RR"):
                    rr = True if rr_w is not None else L.route_respecting(G, routes, M)
                    if rr is None:
                        stats["rr_unknown"] = stats.get("rr_unknown", 0) + 1
                    stats["rr_true"] = stats.get("rr_true", 0) + bool(rr)
                    if rr is False:
                        rr_log.append(dict(g=gname, edges=sorted(G.edges()), routes=routes, M=list(M)))
                    if os.environ.get("RR") == "only":
                        continue
                okp = []
                for R in routes:
                    a, c = (R[0], R[-1]) if R[0] in Mset else (R[-1], R[0])
                    G2 = L.delete_route(G, R)
                    b2 = L.simple_profile(G2, Mset - {a})
                    assert b2[a] == 1 and b2[c] == 1
                    e = L.ext(G2, b2, c, set(R) - {c})
                    if e is None:
                        stats["unknown_ext"] = stats.get("unknown_ext", 0) + 1
                        e = False
                    elif not e:
                        if set(G2[c]) <= set(R):
                            stats["fail_trivial"] = stats.get("fail_trivial", 0) + 1
                        else:
                            stats["fail_nontrivial"] = stats.get("fail_nontrivial", 0) + 1
                            nontriv_log.append(dict(g=gname, edges=sorted(G.edges()), routes=routes, M=list(M), R=R))
                    stats["ext_queries"] += 1
                    stats["ext_true"] += e
                    okp.append(e)
                k = sum(okp)
                hist[k] = hist.get(k, 0) + 1
                if k:
                    stats["close"] += 1
                else:
                    stats["stuck"] += 1
                    stuck_log.append(dict(g=gname, edges=sorted(G.edges()), routes=routes, M=list(M)))
                if k == len(routes):
                    stats["all_p"] += 1
            if os.environ.get("PROGRESS"):
                print("  construction", stats["constructions"], json.dumps(stats), flush=True)
        if stats["graphs"] % 10 == 0:
            print(f"  ... {stats['graphs']} graphs, {time.time() - t0:.0f}s", flush=True)
    stats["hist_num_good_p"] = dict(sorted(hist.items()))
    stats["seconds"] = round(time.time() - t0)
    print(name, json.dumps(stats), flush=True)
    with open(os.path.join(OUT, f"stuck_{name}.jsonl"), "w") as f:
        for s in stuck_log:
            f.write(json.dumps(s) + "\n")
    with open(os.path.join(OUT, f"rrfail_{name}.jsonl"), "w") as f:
        for s in rr_log[:2000]:
            f.write(json.dumps(s) + "\n")
    with open(os.path.join(OUT, f"nontrivial_{name}.jsonl"), "w") as f:
        for s in nontriv_log[:2000]:
            f.write(json.dumps(s) + "\n")
    return stats, stuck_log


def main():
    if os.environ.get("BUDGET"):
        L.BUDGET = int(os.environ["BUDGET"])
        L.FINAL = os.environ.get("FINAL", "1") == "1"
    fam = sys.argv[1]
    ncons = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    maxT = int(sys.argv[3]) if len(sys.argv) > 3 else 64
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    if fam == "order12":
        graphs = families.order12()
    elif fam == "g18":
        graphs = [("G18", families.g18()[0])]
    elif fam == "g2half":
        graphs = [("G2half", families.g2(True)[0])]
    elif fam == "g2full":
        graphs = [("G2full", families.g2(False)[0])]
    elif fam == "blocks":
        cnt = int(os.environ.get("COUNT", "60"))
        graphs = [(f"blocks_{i}", G) for i, G in enumerate(families.block_graphs(cnt, seed))]
    elif fam in ("kprism", "kpetersen"):
        graphs = [(fam, families.kotzig_even("prism" if fam == "kprism" else "petersen"))]
    elif fam == "gbad":
        graphs = [("Gbad", families.gbad()[0])]
    elif fam.startswith("rand"):
        n = int(fam[4:])
        cnt = int(os.environ.get("COUNT", "100"))
        pmin = float(os.environ.get("PMIN", "0.25"))
        pmax = float(os.environ.get("PMAX", "0.7"))
        graphs = [(f"rand{n}_{i}", G) for i, G in enumerate(families.random_graphs(n, cnt, seed + n, pmin, pmax))]
    else:
        raise SystemExit("unknown family")
    fam = fam + os.environ.get("TAG", "") + ("_min" if os.environ.get("TJOIN") == "min" else "") + ("_rr" if os.environ.get("RR") else "")
    run(fam, graphs, ncons, maxT, seed)


if __name__ == "__main__":
    main()
