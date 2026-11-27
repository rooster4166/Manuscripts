"""Check the proposed direct-to-Test1 reduction (forwarded proposal, 2026-11-27).

J: one even vertex z, d(z) = 2m, delta(J) >= 3.  Choose r in N(z), w in N(z)-r, and a matching
M0 = {a_i b_i} (i < m) of J[N(z) - {r, w}].  M = J - zw - {z a_i, z b_i, a_i b_i}.
Claim: if M has a Lovasz decomposition D0 (b(w) = 0, b = 1 elsewhere) with, for each i,
  a_i not in V(Q0(b_i))  or  b_i not in V(Q0(a_i)),
then J - z has a decomposition into k = (n-1)/2 paths with >= 2 ends at r (Test1 at r).

This script (1) searches for such D0 with tools/route_ext.c (query WA: per-end avoidance), and
(2) executes the lift of the proposal (Step 1: delete z; Step 2: append a_i b_i) and verifies the
output independently: an edge partition of J - z into simple paths, count <= k, ends(r) >= 2.
"""
import itertools
import random
import subprocess
import sys

import networkx as nx

ORACLE = sys.argv[1]
BUDGET = 3000000
DEG = int(sys.argv[5]) if len(sys.argv) > 5 else 6


def oracle(lines):
    p = subprocess.run([ORACLE], input="\n".join(lines) + "\n", capture_output=True, text=True)
    return p.stdout.strip().split("\n")


def gen_J(n, rng, pdense=0.9, p=0.35, D=6):
    """Random J on n (odd) vertices: z = 0 with exactly 6 neighbours; N(z) dense; all others odd."""
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
        if min(d for _, d in G.degree()) < 3 or not nx.is_connected(G):
            continue
        if nx.node_connectivity(G) < 3:
            continue
        return G


def perfect_matchings(vs, J):
    if not vs:
        yield []
        return
    a = vs[0]
    for b in vs[1:]:
        if J.has_edge(a, b):
            rest = [v for v in vs[1:] if v != b]
            for pm in perfect_matchings(rest, J):
                yield [(a, b)] + pm


def query_line(M, n, avoid):
    """WA query: profile b(w)=0 (even vertices of M), 1 otherwise; avoid[v] = set of vertices."""
    edges = list(M.edges())
    b = [M.degree(v) % 2 for v in range(n)]
    xs = [sum(1 << u for u in avoid.get(v, ())) for v in range(n)]
    return "WAB %d %d %s %s %s 7 %d" % (n, len(edges), " ".join("%d %d" % e for e in edges),
                                   " ".join(map(str, b)), " ".join(map(str, xs)), BUDGET)


def parse_paths(line):
    parts = line.split("|")
    return [list(map(int, p.split())) for p in parts[1:] if p.strip()]


def lift(J, n, r, w, pairs, D0):
    """Execute Steps 1-2 of the proposal; return a list of paths (vertex lists) of J - z."""
    z = 0
    paths = [list(p) for p in D0]
    # Step 1: delete z.
    iz = [i for i, p in enumerate(paths) if p[0] == z or p[-1] == z]
    assert len(iz) == 1
    P = paths[iz[0]]
    if P[-1] == z:
        P.reverse()
    assert P[1] == r
    if len(P) >= 3:
        paths[iz[0]] = P[1:]
    else:  # Q0(z) = (z, r): drop it and split a path through r
        del paths[iz[0]]
        for i, Q in enumerate(paths):
            if r in Q[1:-1]:
                j = Q.index(r)
                paths[i:i + 1] = [Q[:j + 1], Q[j:]]
                break
        else:
            raise AssertionError("no path through r")
    # Step 2: append a_i b_i at an end.
    for a, bb in pairs:
        done = False
        for v, u in ((bb, a), (a, bb)):
            cand = [i for i, Q in enumerate(paths) if Q[0] == v or Q[-1] == v]
            assert len(cand) == 1, (v, cand)
            Q = paths[cand[0]]
            if u not in Q:
                if Q[0] == v:
                    Q.insert(0, u)
                else:
                    Q.append(u)
                done = True
                break
        if not done:
            return None
    return paths


def verify(J, n, r, paths):
    B = J.copy()
    B.remove_node(0)
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
    k = (n - 1) // 2
    return len(paths) <= k and ends[r] >= 2


def load_resid(path):
    out = []
    for line in open(path):
        line = line.strip()
        if not line or line.startswith('#'):
            continue
        g6 = line.split()[0]
        B = nx.from_graph6_bytes(g6.encode())
        nb = B.number_of_nodes()
        J = nx.relabel_nodes(B, {v: v + 1 for v in B})  # shift so that z = 0
        for u in range(1, 7):
            J.add_edge(0, u)
        out.append(J)
    return out


def main():
    rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
    trials = int(sys.argv[3]) if len(sys.argv) > 3 else 20
    nvals = [int(x) for x in (sys.argv[4] if len(sys.argv) > 4 else "11,13").split(",")]
    stats = dict(roots=0, roots_ok=0, first_ok=0, lift_ok=0, lift_fail=0, nomatch=0)
    RES = load_resid(sys.argv[6]) if len(sys.argv) > 6 else None
    if RES is not None:
        trials = len(RES)
    for t in range(trials):
        if RES is not None:
            J = RES[t]
            n = J.number_of_nodes()
            assert J.degree(0) == 6 and all(J.degree(v) % 2 == 1 for v in J if v != 0), "parity"
        else:
            n = nvals[t % len(nvals)]
            J = gen_J(n, rng, D=DEG)
        U = sorted(J.neighbors(0))
        for r in U:
            stats["roots"] += 1
            found = False
            first = True
            for w in U:
                if w == r:
                    continue
                rest = [u for u in U if u not in (r, w)]
                for pairs in perfect_matchings(rest, J):
                    M = J.copy()
                    M.remove_edges_from([(0, w)] + [(0, x) for p in pairs for x in p] + pairs)
                    lines = []
                    combos = list(itertools.product([0, 1], repeat=len(pairs)))
                    for cb in combos:
                        avoid = {}
                        for (a, bb), o in zip(pairs, cb):
                            if o == 0:
                                avoid[bb] = {a}   # Q0(b) avoids a
                            else:
                                avoid[a] = {bb}   # Q0(a) avoids b
                        lines.append(query_line(M, n, avoid))
                    out = oracle(lines)
                    if any(o.startswith("2") for o in out) and not any(o.startswith("1") for o in out):
                        stats["undecided"] = stats.get("undecided", 0) + 1
                    for o in out:
                        if o.startswith("1"):
                            D0 = parse_paths(o)
                            res = lift(J, n, r, w, pairs, D0)
                            if res is not None and verify(J, n, r, res):
                                stats["lift_ok"] += 1
                            else:
                                stats["lift_fail"] += 1
                                print("LIFT FAIL", list(J.edges()), r, w, pairs, D0, flush=True)
                            found = True
                            break
                    if first:
                        stats["first_ok"] += int(found)
                        first = False
                    if found:
                        break
                if found:
                    break
            if first:
                stats["nomatch"] += 1
            stats["roots_ok"] += int(found)
            if not found and not first:
                print("NO BASE", n, list(J.edges()), "r", r, flush=True)
        print(t, n, stats, flush=True)
    print("FINAL", stats)


if __name__ == "__main__":
    main()
