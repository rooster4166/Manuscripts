"""fb_bruteforce.py: independent brute-force check of the forest base at given roots (session
claude/triangle-base): all Lovász decompositions of M by exact cover of E(M) with simple paths, no
oracle.  usage: fb_bruteforce.py G6 R [G6 R ...]"""
import itertools
import sys

import networkx as nx

from tb import even_vertex
from fb_nodata import tjoin_in_tree


def all_paths(M):
    P = []
    for s in M:
        stack = [[s]]
        while stack:
            p = stack.pop()
            if len(p) >= 2 and p[0] < p[-1]:
                P.append(tuple(p))
            for x in M[p[-1]]:
                if x not in p:
                    stack.append(p + [x])
    return P


def lovasz_decomps(M):
    b = {v: M.degree(v) % 2 for v in M}
    E = [frozenset(e) for e in M.edges()]
    paths = all_paths(M)
    by_edge = {e: [] for e in E}
    for p in paths:
        es = [frozenset(e) for e in zip(p, p[1:])]
        for e in es:
            by_edge[e].append((p, es))
    out = []

    def rec(used, ends, chosen):
        free = [e for e in E if e not in used]
        if not free:
            if all(ends[v] == b[v] for v in M):
                out.append(list(chosen))
            return
        e0 = free[0]
        for p, es in by_edge[e0]:
            if any(e in used for e in es):
                continue
            s, t = p[0], p[-1]
            if ends[s] + 1 > b[s] or ends[t] + 1 > b[t]:
                continue
            ends[s] += 1; ends[t] += 1
            rec(used | set(es), ends, chosen + [p])
            ends[s] -= 1; ends[t] -= 1

    rec(frozenset(), {v: 0 for v in M}, [])
    return out


args = sys.argv[1:]
for g6, r in zip(args[::2], map(int, args[1::2])):
    J = nx.from_graph6_bytes(g6.encode())
    z = even_vertex(J)
    H = J.copy(); H.remove_nodes_from([z, r])
    E = sorted(tuple(sorted(e)) for e in H.edges()); idx = {e: i for i, e in enumerate(E)}
    cyc = []
    for c in nx.cycle_basis(H):
        v = 0
        for a, bb in zip(c, c[1:] + c[:1]):
            v ^= 1 << idx[tuple(sorted((a, bb)))]
        cyc.append(v)
    found = None; nconf = 0; ndec = 0
    for w in sorted(J[z]):
        if w == r:
            continue
        T = [u for u in J[z] if u not in (r, w)]
        phi0 = 0
        for e in tjoin_in_tree(nx.minimum_spanning_tree(H), T):
            phi0 |= 1 << idx[tuple(sorted(e))]
        seen = set()
        for k in range(len(cyc) + 1):
            for comb in itertools.combinations(cyc, k):
                vv = phi0
                for c in comb:
                    vv ^= c
                if vv in seen:
                    continue
                seen.add(vv)
                edges = [E[i] for i in range(len(E)) if vv >> i & 1]
                F = nx.Graph(edges)
                if not nx.is_forest(F):
                    continue
                M = J.copy(); M.remove_edges_from([(z, w)] + [(z, x) for x in T] + edges)
                decs = lovasz_decomps(M)
                ndec += len(decs)
                comps = [sorted(c) for c in nx.connected_components(F)]
                for roots in itertools.product(*[[w] if w in c else c for c in comps]):
                    par = {}
                    for c, rt in zip(comps, roots):
                        for u, x in nx.bfs_edges(F.subgraph(c), rt):
                            par[x] = u
                    nconf += 1
                    for D in decs:
                        endp = {}
                        for p in D:
                            endp.setdefault(p[0], []).append(p); endp.setdefault(p[-1], []).append(p)
                        ok1 = all(par[x] not in endp[x][0] for x in par)
                        ok2 = all(endp[x][0] is not endp[y][0] for x in par for y in par
                                  if x != y and par[x] == par[y])
                        if ok1 and ok2:
                            found = (w, edges, par, D)
                            break
                    if found:
                        break
                if found:
                    break
            if found:
                break
        if found:
            break
    print(g6, "r=%d" % r, "FOUND %s" % (found,) if found else "ABSENT",
          "configurations=%d decompositions_enumerated=%d" % (nconf, ndec), flush=True)
