"""For each graph and each root orbit (under automorphisms), the least |F| in [kmin, kmax] at which
the game (options as fan_game.py) wins; one process per (graph, root), run in parallel."""
import sys, os, subprocess, json
from multiprocessing import Pool
import networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

def orbits(G):
    reps, seen = [], set()
    autos = list(GraphMatcher(G, G).isomorphisms_iter())
    for v in sorted(G):
        if v in seen: continue
        orb = {a[v] for a in autos}
        seen |= orb; reps.append((v, sorted(orb)))
    return reps

def job(args):
    g6, r, kmin, kmax, opts = args
    import resource
    resource.setrlimit(resource.RLIMIT_AS, (3_500_000_000, 3_500_000_000))
    import fan_game as fg
    G = nx.from_graph6_bytes(g6.encode())
    kw = dict(newpath="np" in opts, hubs="hubs" in opts)
    for k in range(kmin, kmax + 1):
        try:
            res = fg.solve_graph(G, k, roots=[r], **kw)
        except MemoryError:
            return g6, r, f"MEMORY at k={k}", None
        if res[r] is not None:
            return g6, r, k, res[r][0]
    return g6, r, None, None

if __name__ == "__main__":
    path, kmin, kmax = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]); opts = sys.argv[4:]
    jobs = []
    for line in open(path):
        g6 = line.strip()
        if not g6: continue
        G = nx.from_graph6_bytes(g6.encode())
        for r, orb in orbits(G):
            jobs.append((g6, r, kmin, kmax, opts))
            print("JOB", g6, "root", r, "orbit", orb, flush=True)
    with Pool(3) as p:
        for g6, r, k, F in p.imap_unordered(job, jobs):
            print("RESULT", g6, "root", r, "k", k, "F", F, flush=True)
    print("DONE", flush=True)
