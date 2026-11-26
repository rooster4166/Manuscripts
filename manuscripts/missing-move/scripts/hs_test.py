"""Test of the hub-strategy conjecture: at every BranchBase3 root (an even vertex with >= 3 even
neighbours and no bridge to a vertex of degree >= 2), the game with path insertion, receipt or
flower and the orbit rule wins with F = a full star plus k <= KMAX edges.
Usage: python3 hs_test.py FILE.g6 KMAX MODE WORKERS [hubroot]   (MODE = R or simple)
With "hubroot" the star is the star of the root y; otherwise it may be centred at any vertex.
Prints the tally of the least k over all root orbits. Lines are printed for LOSE / MEMORY and
k >= 2; with "hubroot" also for k = 1, together with the extra held edges (the edges of F not
at y), for the shape classification of hs_shapes.py."""
import sys, os, resource
from multiprocessing import Pool
import networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

def roots_bb3(G):
    d = dict(G.degree()); ev = {v for v in G if d[v] % 2 == 0 and d[v] > 0}
    bridges = set(frozenset(e) for e in nx.bridges(G))
    out = []
    for y in sorted(ev):
        if sum(1 for w in G[y] if w in ev) < 3:
            continue
        if any(frozenset((y, t)) in bridges and d[t] >= 2 for t in G[y]):
            continue
        out.append(y)
    autos = list(GraphMatcher(G, G).isomorphisms_iter())
    reps, seen = [], set()
    for y in out:
        if y in seen:
            continue
        orb = {a[y] for a in autos}; seen |= orb; reps.append(y)
    return reps

def job(args):
    g6, kmax, mode, hubroot = args
    resource.setrlimit(resource.RLIMIT_AS, (3_000_000_000, 3_000_000_000))
    import fan_game as fg
    fg.CACHE_CAP = 600_000
    G = nx.from_graph6_bytes(g6.encode())
    G = nx.convert_node_labels_to_integers(G)
    res = []
    for y in roots_bb3(G):
        got = "LOSE"
        try:
            for k in range(kmax + 1):
                r = fg.solve_graph(G, k, roots=[y], newpath=True, rf=True, orbit=True, hubs=True,
                                   kmin=k, simple=(mode == "simple"), hubroot=hubroot)
                if r[y] is not None:
                    extra = [e for e in r[y][0] if y not in e]
                    got = f"k={k}" + (f" extra {extra}" if hubroot and k >= 1 else ""); break
        except MemoryError:
            got = "MEMORY"
        res.append((y, got))
    return g6, res

if __name__ == "__main__":
    path, kmax, mode, w = sys.argv[1], int(sys.argv[2]), sys.argv[3], int(sys.argv[4])
    hubroot = len(sys.argv) > 5 and sys.argv[5] == "hubroot"
    lines = [l.strip() for l in open(path) if l.strip()]
    tally = {}
    with Pool(w) as p:
        for g6, res in p.imap_unordered(job, [(g, kmax, mode, hubroot) for g in lines], chunksize=1):
            for y, got in res:
                kk = got.split(" extra")[0]
                tally[kk] = tally.get(kk, 0) + 1
                if kk in ("LOSE", "MEMORY") or kk in ("k=2", "k=3") or (hubroot and kk != "k=0"):
                    print(g6, "root", y, got, flush=True)
    print("TALLY", mode + (" hubroot" if hubroot else ""), "kmax", kmax, tally, flush=True)
