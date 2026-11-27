"""Random tests of Conjecture 3.2 (two even vertices at distance >= 3) and of the packed-even
statement (l1star session).  G(n,p), connected; two (or k) vertices chosen pairwise at distance
>= 3 are kept even, the other even vertices are paired off by toggling edges.  Query: does a path
decomposition with b = deg mod 2 exist?  (l1s ed with an empty avoidance set.)
usage: python3 rand_te3.py N_GRAPHS SEED BUDGET K n1 [n2 ...]     (K = number of even vertices)
"""
import sys, random, subprocess, os, collections, itertools
import networkx as nx
HERE = os.path.dirname(os.path.abspath(__file__))
N, seed, budget, K = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
ns = [int(a) for a in sys.argv[5:]]
rng = random.Random(seed)
p = subprocess.Popen([os.path.join(HERE, "l1s"), "ed", str(budget)], stdin=subprocess.PIPE,
                     stdout=subprocess.PIPE, text=True)
C = collections.Counter()
def packed(G, X):
    return all(not G.has_edge(a, b) and not (set(G[a]) & set(G[b])) for a, b in itertools.combinations(X, 2))
for it in range(N):
    n = rng.choice(ns)
    for _ in range(200):
        G = nx.gnp_random_graph(n, rng.uniform(0.12, 0.35), seed=rng.randrange(1 << 30))
        if not nx.is_connected(G): continue
        X = rng.sample(list(G), K)
        if not packed(G, X): continue
        ev = [v for v in G if G.degree(v) % 2 == 0 and v not in X]
        odd_x = [v for v in X if G.degree(v) % 2 == 1]
        # make X even: toggle an edge from each odd x to a vertex outside N[X]-conflicts later fixed
        rest = ev + odd_x
        if len(rest) % 2: continue
        rng.shuffle(rest)
        for i in range(0, len(rest), 2):
            a, b = rest[i], rest[i + 1]
            if G.has_edge(a, b): G.remove_edge(a, b)
            else: G.add_edge(a, b)
        evs = [v for v in G if G.degree(v) > 0 and G.degree(v) % 2 == 0]
        if sorted(evs) != sorted(X) or not nx.is_connected(G) or not packed(G, X) or G.number_of_edges() > 128:
            continue
        break
    else:
        continue
    E = list(G.edges())
    c = next(v for v in G if G.degree(v) % 2 == 1)
    p.stdin.write(f"{n} {len(E)} " + " ".join(f"{a} {b}" for a, b in E) + f" {c} 0\n"); p.stdin.flush()
    r = int(p.stdout.readline())
    C[f"n={n}"] += 1; C[{1: "ok", 0: "FAIL", 2: "undecided"}[r]] += 1
    if r == 0: print("FAIL", nx.to_graph6_bytes(G, header=False).decode().strip(), X, flush=True)
print("SUMMARY", dict(sorted(C.items())), flush=True)
