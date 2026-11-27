"""exhaust.py -- audit A21: exhaustive checks of the prescribed-end manuscript's computational claims.

usage: python3 exhaust.py N [SOLVER] [--extra] [--slice R/M]

Enumerates all connected graphs of order N (nauty-geng -cq N), keeps those with exactly one vertex
z of positive even degree, and asks the independent solver ts (ts.c) the following queries.

  EE    : u in N(z), d(u) >= 3                     is uz terminal at u?
  away  : x != z, d(x) >= 3, y in N(x), y != z     is xy terminal at x?
          for each failure: y in N(z)?, dist(x,z), xy terminal at y?, reachable?, d(x), d(z)
  reach : every away edge is classified reachable / unreachable, directly from the definition in
          Theorem 6.1: some path z = e0, ..., ek = y whose interior avoids N[x].
With --extra (Remark 7.5 and Section 8 invariants):
  sepee : u in N(z) (all degrees): does K - uz have a Lovasz decomposition separating u and z?
          bucketed by |T|, T = N(u) & N(z)
  tri   : u in N(z), w in T: in K1 = K - {uz, uw, wz},
          (a) separation of w from u and from z,  (b) Q_w avoids {u, z} (hypothesis of Thm 7.2)
  l1p   : c, a odd, a != c, a not adjacent to c: Q_c avoids a; split by g ~ a
  l1s2  : c odd, a1 < a2 of positive degree, not in N[c] u N(g): Q_c avoids {a1, a2}
"""
import sys, os, subprocess, collections, itertools
import networkx as nx

HERE = os.path.dirname(os.path.abspath(__file__))


class Solver:
    def __init__(self, path):
        self.p = subprocess.Popen([path], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)

    def ask(self, G, q):
        nodes = sorted(G.nodes())
        E = list(G.edges())
        line = f"{len(nodes)} {len(E)} " + " ".join(f"{a} {b}" for a, b in E) + " " + q + "\n"
        self.p.stdin.write(line)
        self.p.stdin.flush()
        return int(self.p.stdout.readline())


def reachable(G, z, x, y):
    """Some z--y path with all interior vertices outside N[x] (Theorem 6.1, k >= 1)."""
    if G.has_edge(z, y):
        return True
    Nx = set(G[x]) | {x}
    keep = (set(G.nodes()) - Nx) | {z, y}
    H = G.subgraph(keep)
    return nx.has_path(H, z, y)


def main():
    N = int(sys.argv[1])
    solver = sys.argv[2] if len(sys.argv) > 2 and not sys.argv[2].startswith("--") else os.path.join(HERE, "ts")
    extra = "--extra" in sys.argv
    sl = sys.argv[sys.argv.index("--slice") + 1] if "--slice" in sys.argv else None
    S = Solver(solver)
    C = collections.Counter()
    fail_feats = collections.Counter()
    fails = []
    geng = subprocess.Popen(["nauty-geng", "-cq", str(N)] + ([sl] if sl else []), stdout=subprocess.PIPE, text=True)
    for line in geng.stdout:
        g6 = line.strip()
        G = nx.from_graph6_bytes(g6.encode())
        ev = [v for v in G if G.degree(v) > 0 and G.degree(v) % 2 == 0]
        if len(ev) != 1:
            continue
        z = ev[0]
        C["graphs"] += 1
        if C["graphs"] % 500 == 0:
            print("PROGRESS", dict(C), flush=True)
        Nz = set(G[z])
        d = dict(G.degree())
        dist = nx.single_source_shortest_path_length(G, z)
        # EE
        for u in sorted(Nz):
            if d[u] < 3:
                continue
            C["EE:tests"] += 1
            if S.ask(G, f"T {u} {z}") == 0:
                C["EE:fail"] += 1
                print("EEFAIL", g6, z, u, flush=True)
        # away
        gfail = False
        for x in sorted(G):
            if x == z or d[x] < 3:
                continue
            for y in sorted(G[x]):
                if y == z:
                    continue
                C["away:tests"] += 1
                r = reachable(G, z, x, y)
                C["away:reachable" if r else "away:unreachable"] += 1
                ok = S.ask(G, f"T {x} {y}")
                if ok:
                    continue
                gfail = True
                C["away:fail"] += 1
                C["away:fail_reachable" if r else "away:fail_unreachable"] += 1
                rev = 1 if d[y] < 3 else S.ask(G, f"T {y} {x}")
                f = dict(y_in_Nz=y in Nz, dist_xz=dist[x], rev=rev, reach=r, dx=d[x], dz=d[z])
                fails.append((g6, z, x, y, f))
                print("AWAYFAIL", g6, z, x, y, f, flush=True)
                fail_feats[("y_in_Nz", f["y_in_Nz"])] += 1
                fail_feats[("dist_xz", f["dist_xz"])] += 1
                fail_feats[("terminal_at_y", rev)] += 1
                fail_feats[("dx", d[x])] += 1
                fail_feats[("dz", d[z])] += 1
        if gfail:
            C["graphs_with_away_fail"] += 1
        if not extra:
            continue
        # sepee
        for u in sorted(Nz):
            T = len(Nz & set(G[u]))
            K = G.copy(); K.remove_edge(u, z)
            key = "T<=1" if T <= 1 else ("T=2" if T == 2 else "T>=3")
            C[f"sepee:{key}:tests"] += 1
            if S.ask(K, f"S 1 {u} {z}") == 0:
                C[f"sepee:{key}:fail"] += 1
        # triangles
        for u in sorted(Nz):
            for w in sorted(Nz & set(G[u])):
                K1 = G.copy(); K1.remove_edges_from([(u, z), (u, w), (w, z)])
                C["tri:tests"] += 1
                if S.ask(K1, f"S 2 {w} {u} {w} {z}") == 0:
                    C["tri:sep_fail"] += 1
                if S.ask(K1, f"A {w} 2 {u} {z}") == 0:
                    C["tri:hyp_fail"] += 1
                    print("TRIHYPFAIL", g6, z, u, w, flush=True)
        # l1p
        g = z
        odd = [v for v in G if d[v] % 2 == 1]
        for c in odd:
            for a in odd:
                if a == c or G.has_edge(c, a):
                    continue
                ga = G.has_edge(g, a)
                k = "l1p:g~a" if ga else "l1p:g!~a"
                C[k + ":tests"] += 1
                if S.ask(G, f"A {c} 1 {a}") == 0:
                    C[k + ":fail"] += 1
        # l1s2
        for c in odd:
            bad = set(G[c]) | {c} | set(G[g])
            cand = [v for v in G if v not in bad and d[v] > 0]
            for a1, a2 in itertools.combinations(sorted(cand), 2):
                C["l1s2:tests"] += 1
                if S.ask(G, f"A {c} 2 {a1} {a2}") == 0:
                    C["l1s2:fail"] += 1
                    print("L1S2FAIL", g6, g, c, a1, a2, flush=True)
    for k in sorted(C):
        print(f"{k} = {C[k]}")
    for k in sorted(fail_feats):
        print(f"failfeat {k} = {fail_feats[k]}")
    out = os.path.join(HERE, f"fails{N}" + (f"_{sl.replace('/', 'of')}" if sl else "") + ".txt")
    with open(out, "w") as fh:
        for g6, z, x, y, f in fails:
            fh.write(f"{g6} z={z} x={x} y={y} {f}\n")


if __name__ == "__main__":
    main()
