"""E22 (A): STL(r), BAL(r) and Test1(r) on graphs with exactly one even vertex.

For each graph J (graph6 on stdin or file), with z its unique even vertex and each r in N(z):
  ST     : J has a star-terminal Lovasz decomposition at all
  SS     : ... a star-terminal one with a length-2 path through z
  STL(r) : star-terminal, and r long or some SS transition         (=> Test1(r))
  BAL(r) : Lovasz, #LL + [r short] <= #SS                         (=> Test1(r))
  T1(r)  : Test1 at r itself (exact, via profiles on J - z)
Prints a summary by class (all / 3-connected / 3-connected with J-z free of matching cuts)
and writes failures as JSON lines.
"""
import sys, json, itertools, collections
import networkx as nx
from common import Oracle, even_vertices, relabel, has_matching_cut_fast

orc = Oracle()


def lovasz_prof(J):
    return {v: J.degree(v) % 2 for v in J}


def test1(J, z, r, budget_ok=True):
    """Exact Test1: J - z has <= (n-1)/2 paths with >= 2 ends at r.
    Enumerate profiles on H = J - z with parity, b(r) >= 2, sum exactly n - 1 (upward closure)."""
    H = J.copy(); H.remove_node(z)
    H = nx.relabel_nodes(H, {v: i for i, v in enumerate(sorted(H))})
    mp = {v: i for i, v in enumerate(sorted(set(J) - {z}))}
    n = J.number_of_nodes(); target = n - 1
    rr = mp[r]
    base = {v: H.degree(v) % 2 for v in H}
    base[rr] = 2
    if H.degree(rr) < 2:
        return 0
    extra = target - sum(base.values())
    if extra < 0:
        return 0
    verts = list(H)
    units = extra // 2
    seen = set()
    # distribute `units` increments of 2 (with repetition); also allow fewer if capped by degrees
    for k in range(units, -1, -1):
        found_any = False
        for combo in itertools.combinations_with_replacement(verts, k):
            b = dict(base)
            ok = True
            for v in combo:
                b[v] += 2
                if b[v] > H.degree(v):
                    ok = False; break
            if not ok:
                continue
            found_any = True
            key = tuple(b[v] for v in verts)
            if key in seen:
                continue
            seen.add(key)
            if orc.query(H, b, -1, -1, 0, 0) == 1:
                return 1
        if found_any:
            # every realisable profile of smaller sum lifts to one of this sum (split at an
            # interior visit), unless degree caps prevent it; we only drop k when no profile fits
            return 0
    return 0


def run(graphs, outname, tag):
    stats = collections.Counter()
    fails = open(outname, 'w')
    for g6 in graphs:
        J = relabel(nx.from_graph6_bytes(g6))
        ev = even_vertices(J)
        if len(ev) != 1:
            continue
        z = ev[0]
        n = J.number_of_nodes()
        if J.degree(z) == 0:
            continue
        conn = nx.node_connectivity(J)
        c3 = conn >= 3
        mc = has_matching_cut_fast(J.subgraph(set(J) - {z})) if c3 else None
        classes = ['all'] + (['3c'] if c3 else []) + (['3c_nomc'] if c3 and not mc else [])
        prof = lovasz_prof(J)
        st = orc.query(J, prof, z, -1, 1, 99)
        ss = orc.query(J, prof, z, -1, 1, -1)
        for c in classes:
            stats[(c, 'graphs')] += 1
            stats[(c, 'ST')] += st
            stats[(c, 'SS')] += ss
        for r in sorted(J[z]):
            stl = orc.query(J, prof, z, r, 1, 0)
            bal = orc.query(J, prof, z, r, 0, 0) if not stl else 1
            for c in classes:
                stats[(c, 'pairs')] += 1
                stats[(c, 'STL')] += stl
                stats[(c, 'BAL')] += bal
            if not stl or not bal:
                t1 = test1(J, z, r)
                rec = dict(g6=g6.decode(), n=n, z=z, r=r, dz=J.degree(z), dr=J.degree(r), conn=conn,
                           mc=mc, ST=st, SS=ss, STL=stl, BAL=bal, T1=t1,
                           degN=sorted(J.degree(w) for w in J[z]))
                fails.write(json.dumps(rec) + '\n'); fails.flush()
                for c in classes:
                    stats[(c, 'T1fail')] += (1 - t1)
                    stats[(c, 'STLfail_T1ok')] += (1 - stl) * t1
                    stats[(c, 'BALfail')] += (1 - bal)
    fails.close()
    for c in ('all', '3c', '3c_nomc'):
        if stats[(c, 'graphs')]:
            print(f"[{tag}] {c}: graphs {stats[(c,'graphs')]}, ST {stats[(c,'ST')]}, SS {stats[(c,'SS')]}, "
                  f"pairs {stats[(c,'pairs')]}, STL {stats[(c,'STL')]}, BAL {stats[(c,'BAL')]}, "
                  f"BALfail {stats[(c,'BALfail')]}, T1fail {stats[(c,'T1fail')]}, "
                  f"STLfail-but-T1 {stats[(c,'STLfail_T1ok')]}", flush=True)
    return stats


if __name__ == '__main__':
    fn = sys.argv[1]; out = sys.argv[2]
    if fn == 'P3':
        graphs = [nx.to_graph6_bytes(nx.path_graph(3), header=False).strip()]
    else:
        graphs = [l.strip() for l in open(fn, 'rb') if l.strip()]
    run(graphs, out, fn)
