"""disj_general.py: the disjunctive end-path condition in arbitrary graphs with one even vertex
(session claude/triangle-base).

DL1(k): G has exactly one vertex g of positive even degree; (a_1, b_1), ..., (a_k, b_k) are
disjoint pairs of odd vertices with a_i b_i not an edge.  Is there a Lovasz decomposition with,
for every i, a_i not in Q(b_i) or b_i not in Q(a_i)?

The triangle base (direct-test1 Conj 3.1) is DL1(m-1) on M with the pairs of M0 (and g = w).  This
script decides DL1(1) for every admissible pair and DL1(2) for every admissible pair of pairs,
exactly (tools/route_ext.c, query A), and prints the failures with the local structure:
  d(a,b), common neighbours, adjacency of a, b to g, whether a or b is adjacent to the other pair.

usage: disj_general.py ORACLE FILE.g6 K [--maxpp N] [--budget B]
"""
import argparse
import itertools
from collections import Counter

import networkx as nx

from tb import avoid_query, run_oracle


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("oracle")
    ap.add_argument("file")
    ap.add_argument("k", type=int)
    ap.add_argument("--budget", type=int, default=0)
    ap.add_argument("--conn", type=int, default=1)
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--allodd", action="store_true", help="graphs with no even vertex instead")
    ap.add_argument("--stride", type=int, default=1)
    args = ap.parse_args()
    C = Counter()
    ng = 0
    for line in open(args.file):
        line = line.strip()
        if not line:
            continue
        nline = C["lines"] = C["lines"] + 1
        if (nline - 1) % args.stride:
            continue
        G = nx.convert_node_labels_to_integers(nx.from_graph6_bytes(line.encode()))
        n = G.number_of_nodes()
        ev = [v for v in G if G.degree(v) > 0 and G.degree(v) % 2 == 0]
        if len(ev) != (0 if args.allodd else 1) or any(G.degree(v) == 0 for v in G):
            continue
        if args.conn > 1 and nx.node_connectivity(G) < args.conn:
            continue
        ng += 1
        if args.limit and ng > args.limit:
            break
        g = ev[0] if ev else -1
        C["graphs"] += 1
        odd = [v for v in G if G.degree(v) % 2 == 1]
        pairs = [(a, b) for a, b in itertools.combinations(odd, 2) if not G.has_edge(a, b)]
        if args.k == 1:
            qs = []
            for a, b in pairs:
                qs.append(avoid_query(G, n, {b: {a}}, args.budget, witness=False))
                qs.append(avoid_query(G, n, {a: {b}}, args.budget, witness=False))
            out = [o.strip() for o in run_oracle(args.oracle, qs)]
            for i, (a, b) in enumerate(pairs):
                o1, o2 = out[2 * i], out[2 * i + 1]
                C["inst"] += 1
                if o1 == "1" and o2 == "1":
                    C["both"] += 1
                elif o1 == "1" or o2 == "1":
                    C["one"] += 1
                elif "2" in (o1, o2):
                    C["undec"] += 1
                else:
                    C["FAIL"] += 1
                    cn = sorted(set(G[a]) & set(G[b]))
                    print("FAIL1 %s g=%d a=%d b=%d da=%d db=%d cn=%s ag=%d bg=%d kappa=%d" % (
                        line, g, a, b, G.degree(a), G.degree(b), cn, int(G.has_edge(a, g)),
                        int(G.has_edge(b, g)), nx.node_connectivity(G)), flush=True)
        else:
            # pairs of disjoint pairs: decide the joint disjunction (4 orientations) and the
            # single disjunctions
            single = {}
            qs = []
            for a, b in pairs:
                qs.append(avoid_query(G, n, {b: {a}}, args.budget, witness=False))
                qs.append(avoid_query(G, n, {a: {b}}, args.budget, witness=False))
            out = [o.strip() for o in run_oracle(args.oracle, qs)]
            for i, p in enumerate(pairs):
                single[p] = "1" in (out[2 * i], out[2 * i + 1])
            pp = [(p, q) for p, q in itertools.combinations(pairs, 2) if not set(p) & set(q)]
            qs = []
            for (a1, b1), (a2, b2) in pp:
                for o1, o2 in itertools.product([0, 1], repeat=2):
                    av = {}
                    if o1 == 0:
                        av.setdefault(b1, set()).add(a1)
                    else:
                        av.setdefault(a1, set()).add(b1)
                    if o2 == 0:
                        av.setdefault(b2, set()).add(a2)
                    else:
                        av.setdefault(a2, set()).add(b2)
                    qs.append(avoid_query(G, n, av, args.budget, witness=False))
            out = [o.strip() for o in run_oracle(args.oracle, qs)]
            for i, (p, q) in enumerate(pp):
                o = out[4 * i:4 * i + 4]
                C["inst"] += 1
                if "1" in o:
                    C["joint_ok"] += 1
                    continue
                if "2" in o:
                    C["undec"] += 1
                    continue
                if single[p] and single[q]:
                    C["COMPAT_FAIL"] += 1
                    (a1, b1), (a2, b2) = p, q
                    cross = [(x, y) for x in p for y in q if G.has_edge(x, y)]
                    cn1 = sorted(set(G[a1]) & set(G[b1]))
                    cn2 = sorted(set(G[a2]) & set(G[b2]))
                    print("COMPAT %s g=%d p=%s q=%s cross=%s cn1=%s cn2=%s pg=%s qg=%s kappa=%d" % (
                        line, g, p, q, cross, cn1, cn2,
                        [int(G.has_edge(x, g)) for x in p], [int(G.has_edge(x, g)) for x in q],
                        nx.node_connectivity(G)), flush=True)
                else:
                    C["single_fail"] += 1
    print("SUMMARY", dict(sorted(C.items())), flush=True)


if __name__ == "__main__":
    main()
