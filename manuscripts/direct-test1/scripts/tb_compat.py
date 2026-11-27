"""tb_compat.py: orientation and multi-pair compatibility statistics for the triangle base
(session claude/triangle-base).

For every J, root r and data choice (w, M0) it decides exactly (route_ext.c, query A):
  * for each orientation o in {0,1}^(m-1): is there a Lovasz decomposition of M with, for every i,
    Q0(b_i) avoiding a_i (o_i = 0) or Q0(a_i) avoiding b_i (o_i = 1)?   ('orientation sat')
  * for each single pair i: the disjunction of pair i alone (other pairs unconstrained);
  * joint: some orientation is satisfiable (the triangle base for this data choice).
It also records the local structure of each pair in M: whether a_i, b_i have a common neighbour
in M, whether a_i ~ w, b_i ~ w, and the common neighbours with z's other neighbours.

Output lines: DATA <graph6> r w pairs | orient=<bits of satisfiable orientations> single=<bits>
joint=<0/1> | struct ...   and a SUMMARY.  Raw output is regenerable; keep it out of git.

usage: tb_compat.py ORACLE FILE [--conn 3] [--mind 4] [--budget 0] [--resid]
"""
import argparse
import itertools
import sys
from collections import Counter

import networkx as nx

from tb import base_graph, data_choices, even_vertex, run_oracle, avoid_query


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("oracle")
    ap.add_argument("file")
    ap.add_argument("--conn", type=int, default=3)
    ap.add_argument("--mind", type=int, default=4)
    ap.add_argument("--budget", type=int, default=0)
    ap.add_argument("--resid", action="store_true")
    ap.add_argument("--quiet", action="store_true")
    args = ap.parse_args()
    C = Counter()
    for line in open(args.file):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        G = nx.from_graph6_bytes(line.split()[0].encode())
        if args.resid:
            J = nx.relabel_nodes(G, {v: v + 1 for v in G})
            for u in range(1, 7):
                J.add_edge(0, u)
        else:
            J = G
        J = nx.convert_node_labels_to_integers(J, ordering="sorted")
        n = J.number_of_nodes()
        z = even_vertex(J)
        if z is None or J.degree(z) < args.mind:
            continue
        if args.conn and nx.node_connectivity(J) < args.conn:
            continue
        C["graphs"] += 1
        g6 = nx.to_graph6_bytes(J, header=False).decode().strip()
        for r in sorted(J.neighbors(z)):
            C["roots"] += 1
            root_joint = False
            for w, pairs in data_choices(J, z, r):
                C["data"] += 1
                C["data_m%d" % (len(pairs) + 1)] += 1
                M = base_graph(J, z, w, pairs)
                qs = []
                orients = list(itertools.product([0, 1], repeat=len(pairs)))
                for cb in orients:
                    avoid = {}
                    for (a, bb), o in zip(pairs, cb):
                        if o == 0:
                            avoid.setdefault(bb, set()).add(a)
                        else:
                            avoid.setdefault(a, set()).add(bb)
                    qs.append(avoid_query(M, n, avoid, args.budget, witness=False))
                singles = []
                if len(pairs) >= 2:
                    for (a, bb) in pairs:
                        singles.append(avoid_query(M, n, {bb: {a}}, args.budget, witness=False))
                        singles.append(avoid_query(M, n, {a: {bb}}, args.budget, witness=False))
                out = run_oracle(args.oracle, qs + singles)
                o_or = [o.strip() for o in out[:len(qs)]]
                o_si = [o.strip() for o in out[len(qs):]]
                if "2" in o_or or "2" in o_si:
                    C["undecided"] += 1
                joint = "1" in o_or
                root_joint |= joint
                C["joint%d" % int(joint)] += 1
                nsat = o_or.count("1")
                C["m%d_orient_sat_%d_of_%d" % (len(pairs) + 1, nsat, len(orients))] += 1
                single_ok = [joint] if len(pairs) == 1 else []
                if len(pairs) >= 2:
                    for i in range(len(pairs)):
                        single_ok.append(o_si[2 * i] == "1" or o_si[2 * i + 1] == "1")
                if len(pairs) >= 2:
                    if all(single_ok) and not joint:
                        C["COMPAT_FAIL"] += 1
                    if not all(single_ok):
                        C["single_fail"] += 1
                # structure of each pair in M
                st = []
                for (a, bb) in pairs:
                    cn = set(M.neighbors(a)) & set(M.neighbors(bb))
                    st.append("cn%d,aw%d,bw%d" % (len(cn), int(M.has_edge(a, w)), int(M.has_edge(bb, w))))
                    C["pair_cn%d" % min(len(cn), 3)] += 1
                if not args.quiet or not joint or (len(pairs) >= 2 and all(single_ok) and not joint):
                    print("DATA %s r=%d w=%d pairs=%s | orient=%s single=%s joint=%d | %s" % (
                        g6, r, w, pairs, "".join(o_or), "".join(o_si), int(joint), " ".join(st)),
                        flush=True)
            C["root_ok%d" % int(root_joint)] += 1
    print("SUMMARY", dict(sorted(C.items())), flush=True)


if __name__ == "__main__":
    main()
