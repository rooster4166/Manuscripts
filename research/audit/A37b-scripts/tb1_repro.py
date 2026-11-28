"""tb1_repro.py -- audit A37b item 7: independent reproduction of the (T1) all-odd base data.

Own filter (a37lib: own graph6 decoder, own 3-connectivity), own perfect matchings, own T-joins,
exact decisions by ./obase (own C decider), own lift and own (T1) check.
Per instance (J, z, r), in tiers as in the manuscript:
  M : some perfect matching of J[N(z)] (r the root of its pair, every orientation of the others)
      has an all-odd base;
  S : some forest T-join with r a root has a base (spanning-tree joins first; then, if the cycle
      space has dimension <= MAXCYC, every forest T-join);
  C : the same with r a child, c(r) >= 2;
  N : none found (exhaustive iff the cycle space was enumerated: printed as NONE-EXH).
usage: python3 tb1_repro.py [MAXCYC] < graph6     (prints per-tier counts; one line per non-M instance)
"""
import itertools
import random
import sys
from collections import Counter

from oddbase_lib import Obase, decide_base, is_forest, lift_and_check, rootings, t1_instances, tjoins
from a37lib import adjacency, g6_decode


def perfect_matchings(vs, adj):
    if not vs:
        yield []
        return
    a = vs[0]
    for b in vs[1:]:
        if b in adj[a]:
            rest = [v for v in vs[1:] if v != b]
            for pm in perfect_matchings(rest, adj):
                yield [(a, b)] + pm


def tree_tjoin(tree_edges, verts, T):
    A = {v: [] for v in verts}
    for a, b in tree_edges:
        A[a].append(b)
        A[b].append(a)
    root = verts[0]
    par = {root: None}
    order = [root]
    for u in order:
        for w in A[u]:
            if w not in par:
                par[w] = u
                order.append(w)
    cnt = {v: int(v in T) for v in verts}
    out = set()
    for u in reversed(order):
        if par[u] is not None:
            if cnt[u] % 2:
                out.add(tuple(sorted((u, par[u]))))
            cnt[par[u]] += cnt[u]
    return frozenset(out)


def spanning_trees(verts, edges, rng, nrand):
    A = {v: [] for v in verts}
    for a, b in edges:
        A[a].append(b)
        A[b].append(a)
    out = []
    for s in verts:
        for mode in ("bfs", "dfs"):
            par = {s: None}
            fr = [s]
            te = []
            while fr:
                u = fr.pop(0) if mode == "bfs" else fr.pop()
                for w in sorted(A[u]):
                    if w not in par:
                        par[w] = u
                        te.append((u, w))
                        fr.append(w)
            out.append(te)
    for _ in range(nrand):
        es = list(edges)
        rng.shuffle(es)
        comp = {v: v for v in verts}

        def find(x):
            while comp[x] != x:
                comp[x] = comp[comp[x]]
                x = comp[x]
            return x
        te = []
        for a, b in es:
            ra, rb = find(a), find(b)
            if ra != rb:
                comp[ra] = rb
                te.append((a, b))
        out.append(te)
    return out


def main():
    maxcyc = int(sys.argv[1]) if len(sys.argv) > 1 else 14
    ob = Obase()
    rng = random.Random(37)
    st = Counter()
    for line in sys.stdin:
        g6 = line.split()[0] if line.strip() else ""
        if not g6:
            continue
        n, E = g6_decode(g6)
        z, rs = t1_instances(n, E)
        if z is None:
            continue
        if len(line.split()) > 1:          # optional: a single root given
            rs = [int(line.split()[1])]
        st["graphs"] += 1
        adj = adjacency(n, E)
        Bverts = [v for v in range(n) if v != z]
        Bedges = [tuple(sorted(e)) for e in E if z not in e]
        T = set(adj[z])
        pms = list(perfect_matchings(sorted(T), adj))
        for r in rs:
            st["instances"] += 1
            found = None
            if pms:
                st["with matching data"] += 1
                for pm in pms:
                    other = [p for p in pm if r not in p]
                    rp = [p for p in pm if r in p][0]
                    a0 = rp[0] if rp[1] == r else rp[1]
                    for o in itertools.product((0, 1), repeat=len(other)):
                        par = {a0: r}
                        for (a, b), oo in zip(other, o):
                            if oo:
                                par[b] = a
                            else:
                                par[a] = b
                        phi = frozenset(tuple(sorted(p)) for p in pm)
                        H, D0 = decide_base(ob, n, Bverts, Bedges, phi, par)
                        if D0 is not None:
                            found = ("M", lift_and_check(E, z, r, n, H, par, list(par), D0))
                            break
                    if found:
                        break
                if not found:
                    st["matching data but no matching base"] += 1
                    print("NOMATCHBASE", g6, z, r, flush=True)
            if not found:
                phis = []
                seen = set()
                for te in spanning_trees(Bverts, Bedges, rng, 60):
                    phi = tree_tjoin(te, Bverts, T)
                    if phi not in seen:
                        seen.add(phi)
                        phis.append(phi)
                cyc = len(Bedges) - len(Bverts) + 1
                exh = cyc <= maxcyc
                if exh:
                    for phi in tjoins(Bverts, Bedges, T):
                        if phi not in seen and is_forest(phi):
                            seen.add(phi)
                            phis.append(phi)
                for tier, want_child in (("S", False), ("C", True)):
                    for phi in phis:
                        for par, order in rootings(phi, r):
                            if (r in par) != want_child:
                                continue
                            H, D0 = decide_base(ob, n, Bverts, Bedges, phi, par)
                            if D0 is not None:
                                found = (tier, lift_and_check(E, z, r, n, H, par, order, D0))
                                break
                        if found:
                            break
                    if found:
                        break
                print("NONM", g6, z, r, found[0] if found else ("NONE-EXH" if exh else "NONE"),
                      "cyc", cyc, flush=True)
            if found:
                st["base " + found[0]] += 1
                st["ends at r = %d" % found[1]] += 1
            else:
                st["no base"] += 1
    print("SUMMARY", dict(sorted(st.items())))


if __name__ == "__main__":
    main()
