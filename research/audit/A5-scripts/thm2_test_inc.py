import sys, random, itertools, time
sys.path.insert(0, '/home/user/Manuscripts/tools')
import networkx as nx
from pathnum import solve, verify_partition
random.seed(7)
def semi_cliques():
    out = []
    for k in (1, 2, 3):
        n = 2*k+1
        allE = list(itertools.combinations(range(n), 2))
        reps = []
        for m in range(k):
            for H in itertools.combinations(allE, m):
                Hg = nx.Graph(); Hg.add_nodes_from(range(n)); Hg.add_edges_from(H)
                if not any(nx.is_isomorphic(Hg, R) for R in reps): reps.append(Hg)
        for Hg in reps:
            J = nx.complete_graph(n); J.remove_edges_from(Hg.edges())
            out.append((k, J, list(Hg.edges())))
    return out
fails = []; tested = 0; t = time.time()
for k, J, H in semi_cliques():
    n = J.number_of_nodes()
    trials = int(sys.argv[1]) if k < 3 else int(sys.argv[2])
    for trial in range(trials):
        nout = random.randint(0, 4 if k == 3 else 5)
        outside = list(range(100, 100 + nout))
        for attempt in range(200):
            L = random.randint(1, n + nout)
            seq = random.sample(list(range(n)) + outside, L)
            if not any(v < n for v in seq): continue
            if len(seq) < 2: continue
            ok = all(not (a < n and b < n and J.has_edge(a, b)) for a, b in zip(seq, seq[1:]))
            if ok: break
        else: continue
        G = J.copy(); G.add_edges_from(zip(seq, seq[1:]))
        if G.number_of_edges() > 30: continue
        a, b = seq[0], seq[-1]
        r = solve(G, budget=k+1, min_ends={a: 1, b: 1}, workers=2, time_limit=120)
        tested += 1
        good = r.status in ('OPTIMAL', 'FEASIBLE') and r.value == k+1 and verify_partition(G, r.paths)
        if not good: fails.append((k, H, seq, r.status, r.value))
        print(f"k={k} H={H} P={seq} status={r.status} value={r.value} good={good}", flush=True)
print(f"Theorem 2 random instances k<=3: tested={tested} failures={len(fails)} {fails[:3]} ({time.time()-t:.0f}s)")
