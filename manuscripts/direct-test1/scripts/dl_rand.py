"""dl_rand.py: Conjecture DL (disjunctive avoidance) on random graphs with one even vertex
(session claude/triangle-base).

Random connected G on n vertices with exactly one vertex g of positive even degree.  Pick k
disjoint pairs of non-adjacent odd vertices, by default inside N(g) (the regime a, b in N(g),
where the fixed-orientation statement L1* is not admissible), skipping universal twins of the
component.  Decide "some Lovasz decomposition has a_i not in Q(b_i) or b_i not in Q(a_i) for all
i" with route_ext.c (query A, all 2^k orientations; budget, several seeds).

usage: dl_rand.py ORACLE N P K SEED COUNT [--budget B] [--anywhere]
"""
import argparse
import itertools
import random
from collections import Counter

import networkx as nx

from tb import avoid_query, run_oracle


def gen(n, p, rng):
    while True:
        G = nx.gnp_random_graph(n, p, seed=rng.randrange(10**9))
        g = rng.randrange(n)
        odd = [v for v in G if v != g and G.degree(v) % 2 == 0]
        rng.shuffle(odd)
        for i in range(0, len(odd) - 1, 2):
            u, v = odd[i], odd[i + 1]
            if G.has_edge(u, v):
                G.remove_edge(u, v)
            else:
                G.add_edge(u, v)
        ev = [v for v in G if G.degree(v) % 2 == 0]
        if ev != [g] or G.degree(g) == 0 or not nx.is_connected(G):
            continue
        return G, g


def univ(G, a, b):
    return set(G[a]) == set(G[b]) == set(G) - {a, b}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("oracle")
    ap.add_argument("n", type=int)
    ap.add_argument("p", type=float)
    ap.add_argument("k", type=int)
    ap.add_argument("seed", type=int)
    ap.add_argument("count", type=int)
    ap.add_argument("--budget", type=int, default=5000000)
    ap.add_argument("--seeds", type=str, default="7,11,13")
    ap.add_argument("--anywhere", action="store_true")
    args = ap.parse_args()
    rng = random.Random(args.seed)
    C = Counter()
    seeds = [int(s) for s in args.seeds.split(",")]
    for t in range(args.count):
        G, g = gen(args.n, args.p, rng)
        n = G.number_of_nodes()
        pool = [v for v in (G if args.anywhere else G[g]) if v != g and G.degree(v) % 2 == 1]
        cand = [(a, b) for a, b in itertools.combinations(pool, 2)
                if not G.has_edge(a, b) and not univ(G, a, b)]
        rng.shuffle(cand)
        pairs = []
        used = set()
        for a, b in cand:
            if a in used or b in used:
                continue
            pairs.append((a, b))
            used |= {a, b}
            if len(pairs) == args.k:
                break
        if len(pairs) < args.k:
            C["skip"] += 1
            continue
        C["inst"] += 1
        avoids = []
        for cb in itertools.product([0, 1], repeat=len(pairs)):
            av = {}
            for (a, b), o in zip(pairs, cb):
                if o == 0:
                    av.setdefault(b, set()).add(a)
                else:
                    av.setdefault(a, set()).add(b)
            avoids.append(av)
        out = ["2"] * len(avoids)
        for sd in seeds:
            todo = [i for i, o in enumerate(out) if o == "2"]
            if not todo:
                break
            res = run_oracle(args.oracle, [avoid_query(G, n, avoids[i], args.budget, seed=sd,
                                                       witness=False) for i in todo])
            for i, o in zip(todo, res):
                out[i] = o.strip()
            if "1" in out:
                break
        if "1" in out:
            C["ok"] += 1
            C["orient_sat_%d" % out.count("1")] += 1
        elif "2" in out:
            C["undec"] += 1
            print("UNDEC", nx.to_graph6_bytes(G, header=False).decode().strip(), g, pairs, flush=True)
        else:
            C["FAIL"] += 1
            print("FAIL", nx.to_graph6_bytes(G, header=False).decode().strip(), g, pairs, flush=True)
        if t % 20 == 19:
            print("PROGRESS", t + 1, dict(C), flush=True)
    print("SUMMARY n=%d p=%.2f k=%d" % (args.n, args.p, args.k), dict(sorted(C.items())), flush=True)


if __name__ == "__main__":
    main()
