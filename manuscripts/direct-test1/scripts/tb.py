"""tb.py: the triangle base conjecture (direct-test1 Conj 3.1) on graph families (session
claude/triangle-base).

For every input J (z = the unique vertex of positive even degree), every root r in N(z) and every
data choice (w, M0) (w in N(z) - r, M0 a perfect matching of J[N(z) - {r, w}] by edges of J), the
base question "M = J - zw - {z a_i, z b_i, a_i b_i} has a Lovasz decomposition with, for every i,
a_i not in Q0(b_i) or b_i not in Q0(a_i)" is decided by 2^(m-1) per-end avoidance queries
(tools/route_ext.c, query A: one query per orientation of the disjunctions).  Every base found is
lifted (Steps 1-2 of Thm 2.1) and the result is verified independently.

Per root the verdict is FOUND (some data choice has a base), ABSENT (every data choice proved to
have none), UNDEC (no base found, some query hit the budget) or NODATA.  With --all every data
choice is decided (statistics of the 'for all data' strengthening).  At an ABSENT root Test1 is
decided exactly (test1_exact) to see whether the triangle base or Test1 itself fails.

usage:
  tb.py ORACLE g6 FILE [--all] [--budget N] [--conn K] [--mind D]
        (graph6 of J itself)
  tb.py ORACLE resid FILE [...]      (graph6 of B = J - z with N(z) = {0..5}, as gen_resid.py)
  tb.py ORACLE edges FILE [...]      (lines 'NO BASE n [edge list] r R' of dtl*.py)
  tb.py ORACLE rand N D SEED COUNT [--pd P] [--p P] [...]  (random 3-connected J, d(z) = D)
"""
import argparse
import ast
import itertools
import random
import subprocess
import sys
import time

import networkx as nx


def run_oracle(oracle, lines):
    if not lines:
        return []
    p = subprocess.run([oracle], input="\n".join(lines) + "\n", capture_output=True, text=True)
    out = p.stdout.strip().split("\n")
    assert len(out) == len(lines), (len(out), len(lines))
    return out


def perfect_matchings(vs, J):
    if not vs:
        yield []
        return
    a = vs[0]
    for b in vs[1:]:
        if J.has_edge(a, b):
            for pm in perfect_matchings([v for v in vs[1:] if v != b], J):
                yield [(a, b)] + pm


def data_choices(J, z, r):
    U = sorted(J.neighbors(z))
    for w in U:
        if w == r:
            continue
        for pm in perfect_matchings([u for u in U if u not in (r, w)], J):
            yield w, pm


def base_graph(J, z, w, pairs):
    M = J.copy()
    M.remove_edges_from([(z, w)] + [(z, x) for p in pairs for x in p] + pairs)
    return M


def avoid_query(M, n, avoid, budget, seed=7, witness=True):
    E = list(M.edges())
    b = [M.degree(v) % 2 for v in range(n)]
    xs = [0] * n
    for v, S in avoid.items():
        for u in S:
            xs[v] |= 1 << u
    return "%sAB %d %d %s %s %s %d %d" % ("W" if witness else "", n, len(E),
                                         " ".join("%d %d" % e for e in E), " ".join(map(str, b)),
                                         " ".join(map(str, xs)), seed, budget)


def parse_paths(line):
    return [list(map(int, p.split())) for p in line.split("|")[1:] if p.strip()]


def check_base(M, n, z, w, pairs, D0):
    """Independent check that D0 is a Lovasz decomposition of M satisfying the disjunctions."""
    used = set()
    ends = {v: 0 for v in range(n)}
    for Q in D0:
        assert len(Q) >= 2 and len(set(Q)) == len(Q)
        for x, y in zip(Q, Q[1:]):
            e = frozenset((x, y))
            assert M.has_edge(x, y) and e not in used
            used.add(e)
        ends[Q[0]] += 1
        ends[Q[-1]] += 1
    assert len(used) == M.number_of_edges()
    assert all(ends[v] == M.degree(v) % 2 for v in range(n))
    endpath = {}
    for Q in D0:
        endpath.setdefault(Q[0], []).append(Q)
        endpath.setdefault(Q[-1], []).append(Q)
    for a, b in pairs:
        ok1 = all(a not in Q for Q in endpath.get(b, []))
        ok2 = all(b not in Q for Q in endpath.get(a, []))
        assert ok1 or ok2


def lift(J, z, r, pairs, D0):
    paths = [list(p) for p in D0]
    iz = [i for i, p in enumerate(paths) if p[0] == z or p[-1] == z]
    assert len(iz) == 1
    P = paths[iz[0]]
    if P[-1] == z:
        P.reverse()
    assert P[1] == r
    if len(P) >= 3:
        paths[iz[0]] = P[1:]
    else:
        del paths[iz[0]]
        for i, Q in enumerate(paths):
            if r in Q[1:-1]:
                j = Q.index(r)
                paths[i:i + 1] = [Q[:j + 1], Q[j:]]
                break
        else:
            raise AssertionError("no path through r")
    for a, bb in pairs:
        for v, u in ((bb, a), (a, bb)):
            cand = [i for i, Q in enumerate(paths) if Q[0] == v or Q[-1] == v]
            assert len(cand) == 1
            Q = paths[cand[0]]
            if u not in Q:
                if Q[0] == v:
                    Q.insert(0, u)
                else:
                    Q.append(u)
                break
        else:
            return None
    return paths


def verify_test1(J, z, r, paths):
    n = J.number_of_nodes()
    B = J.copy()
    B.remove_node(z)
    used = set()
    ends = {v: 0 for v in B}
    for Q in paths:
        assert len(Q) >= 2 and len(set(Q)) == len(Q), Q
        for x, y in zip(Q, Q[1:]):
            e = frozenset((x, y))
            assert B.has_edge(x, y) and e not in used, (Q, x, y)
            used.add(e)
        ends[Q[0]] += 1
        ends[Q[-1]] += 1
    assert len(used) == B.number_of_edges()
    return len(paths) <= (n - 1) // 2 and ends[r] >= 2


def test1_exact(oracle, J, z, r, budget=0):
    """Test1 at r, decided exactly: some profile b on B = J - z with b = deg mod 2, b(r) >= 2,
    sum b <= n - 1, b <= 3, is realisable.  Returns 1, 0 or 2 (budget)."""
    n = J.number_of_nodes()
    B = J.copy()
    B.remove_node(z)
    B = nx.relabel_nodes(B, {v: i for i, v in enumerate(sorted(B))})
    idx = {v: i for i, v in enumerate([u for u in sorted(J) if u != z])}
    nb = n - 1
    E = list(B.edges())
    base = [B.degree(v) % 2 for v in range(nb)]
    ri = idx[r]
    slack = (nb - sum(base)) - (2 - base[ri])  # remaining ends, in units of 1 (always even)
    if slack < 0:
        return 0
    # extra ends: +2 at some vertices (b <= 3), r gets 2 (even) or 3 (odd) at least
    start = list(base)
    start[ri] = 2 if base[ri] == 0 else 3
    rest = nb - sum(start)
    if rest < 0:
        return 0
    cand = [v for v in range(nb) if start[v] + 2 <= 3 and B.degree(v) >= start[v] + 2]
    lines = []
    for k in range(rest // 2 + 1):
        for S in itertools.combinations(cand, k):
            b = list(start)
            for v in S:
                b[v] += 2
            lines.append("PB %d %d %s %s 3 %d" % (nb, len(E), " ".join("%d %d" % e for e in E),
                                                  " ".join(map(str, b)), budget))
    out = run_oracle(oracle, lines)
    if any(o.strip() == "1" for o in out):
        return 1
    if any(o.strip() == "2" for o in out):
        return 2
    return 0


SEEDS = [7]


def decide_data(oracle, J, n, z, r, w, pairs, budget, stats):
    """Return ('FOUND', D0) / ('ABSENT', None) / ('UNDEC', None) for one data choice."""
    M = base_graph(J, z, w, pairs)
    avoids = []
    for cb in itertools.product([0, 1], repeat=len(pairs)):
        avoid = {}
        for (a, bb), o in zip(pairs, cb):
            if o == 0:
                avoid.setdefault(bb, set()).add(a)
            else:
                avoid.setdefault(a, set()).add(bb)
        avoids.append(avoid)
    out = ["2"] * len(avoids)
    for seed in SEEDS:
        todo = [i for i, o in enumerate(out) if o.startswith("2")]
        if not todo:
            break
        res = run_oracle(oracle, [avoid_query(M, n, avoids[i], budget, seed=seed) for i in todo])
        stats["queries"] += len(todo)
        for i, o in zip(todo, res):
            out[i] = o
        if any(o.startswith("1") for o in out):
            break
    for o in out:
        if o.startswith("1"):
            D0 = parse_paths(o)
            check_base(M, n, z, w, pairs, D0)
            res = lift(J, z, r, pairs, D0)
            if res is not None and verify_test1(J, z, r, res):
                stats["lift_ok"] += 1
            else:
                stats["lift_fail"] += 1
                print("LIFT FAIL", list(J.edges()), r, w, pairs, D0, flush=True)
            return "FOUND", D0
    if any(o.startswith("2") for o in out):
        return "UNDEC", None
    assert all(o.strip() == "0" for o in out), out
    return "ABSENT", None


def even_vertex(J):
    ev = [v for v in J if J.degree(v) % 2 == 0 and J.degree(v) > 0]
    return ev[0] if len(ev) == 1 else None


def process(oracle, J, args, stats, tag=""):
    n = J.number_of_nodes()
    assert sorted(J) == list(range(n))
    z = even_vertex(J)
    if z is None:
        return
    if J.degree(z) < args.mind:
        return
    if args.conn and nx.node_connectivity(J) < args.conn:
        return
    stats["graphs"] += 1
    stats["deg%d" % J.degree(z)] = stats.get("deg%d" % J.degree(z), 0) + 1
    roots = sorted(J.neighbors(z)) if args.root is None else [args.root]
    for r in roots:
        if J.degree(r) < 3:
            stats["root_deg1"] += 1
            continue
        stats["roots"] += 1
        verdict = "NODATA"
        ndata = nfound = nabs = nund = 0
        first = None
        for w, pairs in data_choices(J, z, r):
            ndata += 1
            v, _ = decide_data(oracle, J, n, z, r, w, pairs, args.budget, stats)
            if first is None:
                first = v
            if v == "FOUND":
                nfound += 1
            elif v == "ABSENT":
                nabs += 1
            else:
                nund += 1
            if v == "FOUND" and not args.all:
                break
        if ndata == 0:
            stats["nodata"] += 1
            continue
        stats["data"] += ndata
        if nfound:
            verdict = "FOUND"
            stats["found"] += 1
            stats["first_ok"] += int(first == "FOUND")
            if args.all:
                stats["data_found"] += nfound
                stats["data_absent"] += nabs
                stats["data_undec"] += nund
                if nabs == 0 and nund == 0:
                    stats["root_alldata"] += 1
        elif nund:
            verdict = "UNDEC"
            stats["undec"] += 1
        else:
            verdict = "ABSENT"
            stats["absent"] += 1
        if verdict != "FOUND":
            t1 = test1_exact(oracle, J, z, r, budget=args.t1budget) if verdict == "ABSENT" else -1
            stats["absent_test1_%d" % t1] = stats.get("absent_test1_%d" % t1, 0) + 1
            kappa = nx.node_connectivity(J)
            print("ROOT %s %s n=%d d(z)=%d kappa=%d r=%d data=%d abs=%d und=%d test1=%d %s" % (
                verdict, tag, n, J.degree(z), kappa, r, ndata, nabs, nund, t1,
                nx.to_graph6_bytes(J, header=False).decode().strip()), flush=True)


def gen_J(n, D, rng, pdense, p):
    while True:
        G = nx.gnp_random_graph(n, p, seed=rng.randrange(10**9))
        G.remove_edges_from(list(G.edges(0)))
        U = rng.sample(range(1, n), D)
        for u in U:
            G.add_edge(0, u)
        for a, b in itertools.combinations(U, 2):
            if rng.random() < pdense:
                G.add_edge(a, b)
            elif G.has_edge(a, b):
                G.remove_edge(a, b)
        bad = [v for v in range(1, n) if G.degree(v) % 2 == 0]
        rng.shuffle(bad)
        for i in range(0, len(bad), 2):
            u, v = bad[i], bad[i + 1]
            if G.has_edge(u, v):
                G.remove_edge(u, v)
            else:
                G.add_edge(u, v)
        if G.degree(0) != D or any(G.degree(v) % 2 == 0 for v in range(1, n)):
            continue
        if min(d for _, d in G.degree()) < 3 or nx.node_connectivity(G) < 3:
            continue
        return G


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("oracle")
    ap.add_argument("mode", choices=["g6", "resid", "edges", "rand"])
    ap.add_argument("rest", nargs="*")
    ap.add_argument("--all", action="store_true")
    ap.add_argument("--budget", type=int, default=0)
    ap.add_argument("--t1budget", type=int, default=0)
    ap.add_argument("--conn", type=int, default=0)
    ap.add_argument("--mind", type=int, default=4)
    ap.add_argument("--root", type=int, default=None)
    ap.add_argument("--pd", type=float, default=0.9)
    ap.add_argument("--p", type=float, default=0.35)
    ap.add_argument("--seeds", type=str, default="7")
    args = ap.parse_args()
    SEEDS[:] = [int(x) for x in args.seeds.split(",")]
    stats = {k: 0 for k in ("graphs", "roots", "root_deg1", "nodata", "data", "found", "first_ok",
                            "absent", "undec", "queries", "lift_ok", "lift_fail", "data_found",
                            "data_absent", "data_undec", "root_alldata")}
    t0 = time.time()
    if args.mode == "rand":
        n, D, seed, count = map(int, args.rest[:4])
        rng = random.Random(seed)
        for t in range(count):
            J = gen_J(n, D, rng, args.pd, args.p)
            process(args.oracle, J, args, stats, tag="rand%d" % t)
            print("PROGRESS", t, stats, flush=True)
    else:
        for line in open(args.rest[0]):
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            if args.mode == "edges":
                if not line.startswith("NO BASE"):
                    continue
                edges = ast.literal_eval("[" + line.split("[", 1)[1].rsplit("]", 1)[0] + "]")
                J = nx.Graph(edges)
                args.root = int(line.rsplit("r", 1)[1])
            else:
                G = nx.from_graph6_bytes(line.split()[0].encode())
                if args.mode == "resid":
                    J = nx.relabel_nodes(G, {v: v + 1 for v in G})
                    for u in range(1, 7):
                        J.add_edge(0, u)
                else:
                    J = G
            J = nx.convert_node_labels_to_integers(J, ordering="sorted")
            process(args.oracle, J, args, stats, tag=line.split()[0][:24])
    stats["secs"] = round(time.time() - t0, 1)
    print("SUMMARY", stats, flush=True)


if __name__ == "__main__":
    main()
