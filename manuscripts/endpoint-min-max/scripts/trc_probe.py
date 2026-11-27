"""TRC on G_18 (synthesis section 15): Thm 21 pairings from random spanning trees, and the realisability
of their transversals by tools/realis_wide.c (60 s per query).
Usage: python3 manuscripts/endpoint-min-max/scripts/trc_probe.py REALIS_WIDE_BIN SEED TREES PER_PAIRING
"""
import sys, random, subprocess, itertools, time
sys.path.insert(0, 'manuscripts/endpoint-min-max/scripts')
import networkx as nx
from construction import construct, tree_tjoin
import emm_lib as L
BIN = sys.argv[1]
G = nx.from_graph6_bytes(b"Q~?GW\\cCoP?@?A?A?@??N?@w?F_")
D = set(range(10))
n = G.number_of_nodes(); E = list(G.edges())
Ev = L.even_vertices(G)
enc = f"{n} {len(E)} " + " ".join(f"{a} {c}" for a, c in E)
def realisable(M, timeout):
    b = [1 if G.degree(v) % 2 else (2 if v in M else 0) for v in range(n)]
    try:
        out = subprocess.run([BIN], input="P " + enc + " " + " ".join(map(str, b)) + "\n",
                             capture_output=True, text=True, timeout=timeout).stdout.strip()
        return out
    except subprocess.TimeoutExpired:
        return "timeout"
rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
seen = set()
for t in range(int(sys.argv[3]) if len(sys.argv) > 3 else 3):
    H = G.copy()
    for u, w in H.edges(): H[u][w]["weight"] = rng.random()
    J = tree_tjoin(nx.minimum_spanning_tree(H), Ev)
    P, routes = construct(G, J)
    P = [tuple(sorted(p)) for p in P]
    key = tuple(sorted(P))
    if key in seen: continue
    seen.add(key)
    cross = sum((a in D) != (c in D) for a, c in P)
    trans = [set(ch) for ch in itertools.product(*P)]
    trans.sort(key=lambda M: len(M & D))
    print("pairing", P, "crossing the gadget cut:", cross, "| min marks in D over transversals:", len(trans[0] & D), flush=True)
    res = {}
    t0 = time.time()
    for M in trans[:int(sys.argv[4]) if len(sys.argv) > 4 else 16]:
        r = realisable(M, 60)
        res[r] = res.get(r, 0) + 1
        if r != "1":
            print("   transversal", sorted(M), "marks in D", len(M & D), "->", r, flush=True)
    print("   tested", sum(res.values()), "results", res, f"{time.time()-t0:.0f}s", flush=True)
