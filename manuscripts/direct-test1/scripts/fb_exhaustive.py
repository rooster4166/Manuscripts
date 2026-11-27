"""fb_exhaustive.py: exhaustive forest-base check at given roots (session claude/triangle-base).
For every w, EVERY forest T-join of H = J - {z, r} (T-join + cycle space, acyclic ones kept) and
EVERY admissible rooting, query route_ext C (conditions (i), (ii)); exact search (budget 0).
usage: fb_exhaustive.py ORACLE LOG   (lines 'NOFB <g6> r=<r> ...' of fb_nodata.py)"""
import itertools
import sys

import networkx as nx

from tb import even_vertex, run_oracle, parse_paths, verify_test1
from fb_nodata import tjoin_in_tree, forest_lift

oracle, log = sys.argv[1], sys.argv[2]
for line in open(log):
    if not line.startswith("NOFB"):
        continue
    g6 = line.split()[1]
    r = int(line.split("r=")[1].split()[0])
    J = nx.from_graph6_bytes(g6.encode())
    z = even_vertex(J)
    n = J.number_of_nodes()
    H = J.copy()
    H.remove_nodes_from([z, r])
    E = sorted(tuple(sorted(e)) for e in H.edges())
    idx = {e: i for i, e in enumerate(E)}
    cyc = []
    for c in nx.cycle_basis(H):
        vec = 0
        for a, b in zip(c, c[1:] + c[:1]):
            vec ^= 1 << idx[tuple(sorted((a, b)))]
        cyc.append(vec)
    verdict, tried = "ABSENT", 0
    for w in sorted(J[z]):
        if w == r or verdict == "FOUND":
            continue
        T = [u for u in J[z] if u not in (r, w)]
        S = nx.minimum_spanning_tree(H)
        phi0 = 0
        for e in tjoin_in_tree(S, T):
            phi0 |= 1 << idx[tuple(sorted(e))]
        forests = []
        for k in range(len(cyc) + 1):
            for comb in itertools.combinations(cyc, k):
                v = phi0
                for c in comb:
                    v ^= c
                edges = [E[i] for i in range(len(E)) if v >> i & 1]
                F = nx.Graph(edges)
                if nx.is_forest(F):
                    forests.append(edges)
        for edges in forests:
            if verdict == "FOUND":
                break
            F = nx.Graph(edges)
            comps = [sorted(c) for c in nx.connected_components(F)]
            M = J.copy()
            M.remove_edges_from([(z, w)] + [(z, v) for v in T] + edges)
            ME = list(M.edges())
            b = [M.degree(v) % 2 for v in range(n)]
            pars, qs = [], []
            for roots in itertools.product(*[[w] if w in c else c for c in comps]):
                par = {}
                for c, rt in zip(comps, roots):
                    for u, v in nx.bfs_edges(F.subgraph(c), rt):
                        par[v] = u
                rv = [1 << v for v in range(n)]
                for v, p in par.items():
                    rv[v] |= 1 << p
                pars.append(par)
                qs.append("WCB %d %d %s %s %s 7 0" % (n, len(ME), " ".join("%d %d" % e for e in ME),
                          " ".join(map(str, b)), " ".join(map(str, rv))))
            tried += len(qs)
            for par, o in zip(pars, run_oracle(oracle, qs)):
                if o.startswith("1"):
                    res = forest_lift(J, z, r, par, parse_paths(o))
                    verdict = "FOUND (lift %s)" % ("ok" if verify_test1(J, z, r, res) else "FAIL")
                    break
    print(g6, "r=%d" % r, verdict, "queries=%d" % tried, flush=True)
