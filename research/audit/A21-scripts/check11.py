"""check11.py -- audit A21: the partial order-11 away-failure list.

usage: python3 check11.py FAILFILE.gz SAMPLE SEED [TIMEOUT_SECONDS]

For every line "FAIL g6 x=.. y=.. z=.. away" of the authors' list:
  * z is the only vertex of positive even degree, xy is an edge, y != z, d(x) >= 3;
  * reachability (Theorem 6.1 definition), y in N(z), dist(x, z), d(x), d(z).
For a random sample of SAMPLE lines, re-decide with the independent solver ts (per-query timeout;
an instance over the timeout is reported as undecided):
  * xy terminal at x (expected 0, i.e. a genuine failure);
  * xy terminal at y (the claim of Section 3 / Question 6.5).
"""
import sys, os, gzip, random, collections, subprocess
import networkx as nx
from exhaust import Solver, reachable

HERE = os.path.dirname(os.path.abspath(__file__))


def main():
    path, sample, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    tmo = float(sys.argv[4]) if len(sys.argv) > 4 else 30.0
    rows = []
    with gzip.open(path, "rt") as fh:
        for line in fh:
            p = line.split()
            if not p or p[0] != "FAIL":
                print("non-FAIL line:", line.strip()); continue
            kv = dict(t.split("=") for t in p[2:5])
            rows.append((p[1], int(kv["z"]), int(kv["x"]), int(kv["y"]), p[5]))
    C = collections.Counter()
    for g6, z, x, y, tag in rows:
        G = nx.from_graph6_bytes(g6.encode())
        ev = [v for v in G if G.degree(v) > 0 and G.degree(v) % 2 == 0]
        assert ev == [z] and G.has_edge(x, y) and y != z and G.degree(x) >= 3 and tag == "away", (g6, x, y, z)
        C["rows"] += 1
        C["reachable" if reachable(G, z, x, y) else "unreachable"] += 1
        C[f"y_in_Nz={G.has_edge(y, z)}"] += 1
        C[f"dist_xz={nx.shortest_path_length(G, x, z)}"] += 1
        C[f"dx={G.degree(x)}"] += 1
        C[f"dz={G.degree(z)}"] += 1
    C["distinct_graphs"] = len({r[0] for r in rows})
    for k in sorted(C):
        print(f"{k} = {C[k]}", flush=True)
    C = collections.Counter()
    rng = random.Random(seed)
    for g6, z, x, y, tag in rng.sample(rows, min(sample, len(rows))):
        G = nx.from_graph6_bytes(g6.encode())
        C["sample"] += 1
        C[f"sample_terminal_at_x={ask_timed(G, f'T {x} {y}', tmo)}"] += 1
        C[f"sample_terminal_at_y={1 if G.degree(y) < 3 else ask_timed(G, f'T {y} {x}', tmo)}"] += 1
    for k in sorted(C):
        print(f"{k} = {C[k]}")


def ask_timed(G, q, tmo):
    """One query in its own ts process; 'undecided' if it exceeds tmo seconds."""
    E = list(G.edges())
    line = f"{G.number_of_nodes()} {len(E)} " + " ".join(f"{a} {b}" for a, b in E) + " " + q + "\n"
    try:
        r = subprocess.run([os.path.join(HERE, "ts")], input=line, capture_output=True, text=True, timeout=tmo)
        return r.stdout.strip()
    except subprocess.TimeoutExpired:
        return "undecided"


if __name__ == "__main__":
    main()
