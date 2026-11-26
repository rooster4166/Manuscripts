"""EMC and the transfer-extension hypothesis on all connected graphs of even order n.

For each connected G of even order (data/conn{n}.g6) this computes the realisable family F(G)
with the exact oracle tools/realis.c and reports:

  * EMC (critical G, i.e. no realisable set of size < e/2): the minimal members of F(G) all
    have size e/2, satisfy basis exchange, and every even vertex lies in one (loopless).
  * Transfer test at the critical level.  For every even y with m >= 2 even neighbours
    (the BranchBase case) and every even neighbour a of y with ya not a bridge, put
    K = G - ya and P = N_E(y) - a.  The single Fan transfer of ya towards y turns a
    realisable S_K of K with P <= S_K into the realisable set S_K + y of G
    (KStep.lean, realisable_transfer).  The test asks for such S_K with |S_K| <= e/2 - 1,
    so that |S_K + y| <= e/2: the rooted test (R) at y.
    'ext' = some a works.  'fail' instances are listed.

Usage: python3 tools/emc_sweep.py N [workers]
"""
import sys
import os
from itertools import combinations
from multiprocessing import Pool

import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import realis


def is_matroid_bases(B):
    B = set(B)
    for X in B:
        for Y in B:
            for x in X - Y:
                if not any(((X - {x}) | {y}) in B for y in Y - X):
                    return False
    return True


def analyse(line):
    G = nx.convert_node_labels_to_integers(nx.from_graph6_bytes(line.encode()))
    n = G.number_of_nodes()
    Ev, fam = realis.family(G)
    e = len(Ev)
    out = {"g6": line, "e": e}
    if e == 0:
        return out
    fam = set(fam)
    minimal = [S for S in fam if not any((S - {v}) in fam for v in S)]
    sizes = sorted({len(S) for S in minimal})
    critical = sizes[0] == e // 2 if sizes else False
    out["critical"] = critical
    if critical:
        out["emc"] = (sizes == [e // 2] and is_matroid_bases(minimal)
                      and set().union(*minimal) == set(Ev))
        out["uniform"] = len(minimal) == len(list(combinations(Ev, e // 2)))
    # transfer test, critical level
    deg = dict(G.degree())
    evset = set(Ev)
    trans = []
    for y in Ev:
        NE = [a for a in G[y] if a in evset]
        if len(NE) < 2:
            continue
        rooted = any(y in S and len(S) <= e // 2 for S in fam)
        ok_a = []
        for a in NE:
            K = G.copy()
            K.remove_edge(y, a)
            if not nx.is_connected(K):
                continue
            _, famK = realis.family(K)
            P = set(NE) - {a}
            if any(P <= S and len(S) <= e // 2 - 1 for S in famK):
                ok_a.append(a)
        trans.append((y, len(NE), rooted, ok_a))
    out["trans"] = trans
    return out


def init():
    realis._proc = None


def main():
    N = int(sys.argv[1])
    workers = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    lines = [l.strip() for l in open(f"data/conn{N}.g6") if l.strip()]
    stats = {"graphs": 0, "critical": 0, "emc": 0, "uniform": 0,
             "inst": 0, "inst_crit": 0, "ext": 0, "fail": 0}
    by_m = {}
    fails = []
    with Pool(workers, initializer=init) as pool:
        for i, out in enumerate(pool.imap_unordered(analyse, lines, chunksize=20)):
            stats["graphs"] += 1
            if out.get("critical"):
                stats["critical"] += 1
                stats["emc"] += out["emc"]
                stats["uniform"] += out["uniform"]
                if not out["emc"]:
                    print("EMC FAIL", out["g6"], flush=True)
            for (y, m, rooted, ok_a) in out.get("trans", []):
                stats["inst"] += 1
                crit = out.get("critical", False)
                stats["inst_crit"] += crit
                d = by_m.setdefault((m, crit), [0, 0])
                d[0] += 1
                if ok_a:
                    stats["ext"] += 1
                else:
                    d[1] += 1
                    stats["fail"] += 1
                    fails.append((out["g6"], y, m, crit, rooted))
            if (i + 1) % 1000 == 0:
                print("progress", i + 1, stats, flush=True)
    print("n =", N, stats)
    print("by (m, critical): [instances, transfer failures]", dict(sorted(by_m.items())))
    for f in fails[:60]:
        print("FAIL g6=%s y=%d m=%d critical=%s rooted=%s" % f)
    print("total transfer failures", len(fails))


if __name__ == "__main__":
    main()
