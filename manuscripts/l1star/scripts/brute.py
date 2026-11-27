"""Independent brute force for small graphs: enumerate all Lovász decompositions.
A decomposition is built by choosing, at every vertex, a set of transitions (pairs of incident
edges that are consecutive on a path); the trails formed must be paths, and the number of path
ends at v must be deg(v) mod 2.  Used to cross-check l1s (mode ed) on small graphs.
"""
import itertools, sys
import networkx as nx

def lovasz_decomps(G):
    V = list(G); E = [tuple(sorted(e)) for e in G.edges()]
    inc = {v: [e for e in E if v in e] for v in V}
    # at each vertex choose a partial matching on incident edges leaving exactly d mod 2 unmatched
    def matchings(lst, unmatched):
        if not lst:
            if unmatched == 0: yield []
            return
        a = lst[0]
        if unmatched > 0:
            for m in matchings(lst[1:], unmatched - 1): yield m
        for i in range(1, len(lst)):
            rest = lst[1:i] + lst[i+1:]
            for m in matchings(rest, unmatched): yield [(a, lst[i])] + m
    choices = [list(matchings(inc[v], G.degree(v) % 2)) for v in V]
    for combo in itertools.product(*choices):
        nxt = {}  # (edge, vertex) -> next edge through vertex
        for v, ms in zip(V, combo):
            for a, b in ms:
                nxt[(a, v)] = b; nxt[(b, v)] = a
        seen = set(); paths = []; ok = True
        for e in E:
            if e in seen: continue
            # walk to one end
            cur, came = e, None
            # find an end: go along transitions from e via e[0]
            def walk(e0, v0):
                seq = [e0]; v = v0; ee = e0
                while (ee, v) in nxt:
                    ee = nxt[(ee, v)]
                    if ee == e0: return None
                    seq.append(ee); v = ee[0] if ee[1] == v else ee[1]
                return seq, v
            r1 = walk(e, e[0]); r2 = walk(e, e[1])
            if r1 is None or r2 is None: ok = False; break
            s1, end1 = r1; s2, end2 = r2
            trail = list(reversed(s2)) + s1[1:]
            # vertex sequence from end2 to end1
            vs = [end2]; v = end2
            for ee in trail:
                v = ee[0] if ee[1] == v else ee[1]; vs.append(v)
            if len(set(vs)) != len(vs): ok = False; break
            for ee in trail: seen.add(ee)
            paths.append(vs)
        if ok: yield paths

if __name__ == "__main__":
    G = nx.from_graph6_bytes(sys.argv[1].encode()); c = int(sys.argv[2]); A = set(map(int, sys.argv[3].split(',')))
    for P in lovasz_decomps(G):
        Qc = [p for p in P if p[0] == c or p[-1] == c]
        if all(not (set(q) & A) for q in Qc): print(P)
