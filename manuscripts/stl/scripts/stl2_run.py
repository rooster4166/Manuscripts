"""E22 (B): the Test2 analogue.  J has exactly two even vertices z, r, adjacent; n even.

Decompositions D of J with b(z) = 0, b(r) = beta in {0, 2}, b(v) = 1 otherwise (|D| = (n-2+beta)/2).
  STL2(z,r) : some such D is star-terminal at z with [r short] <= #SS       (=> Test2)
  BAL2(z,r) : some such D has #LL + [r short] <= #SS                         (=> Test2)
  P0        : some D with beta = 0 exists at all
  T2        : Test2 itself: J - z has <= n/2 paths with >= 3 ends at r (exact, via profiles)
Each graph gives two instances, (z, r) and (r, z).
"""
import sys, json, itertools, collections
import networkx as nx
from common import Oracle, even_vertices, relabel, has_matching_cut_fast

orc = Oracle()


def test2(J, z, r):
    mp = {v: i for i, v in enumerate(sorted(set(J) - {z}))}
    H = nx.relabel_nodes(J.subgraph(set(J) - {z}).copy(), mp)
    n = J.number_of_nodes(); target = n
    rr = mp[r]
    if H.degree(rr) < 3:
        return 0
    base = {v: H.degree(v) % 2 for v in H}
    base[rr] = 3
    extra = target - sum(base.values())
    if extra < 0:
        return 0
    verts = list(H)
    for k in range(extra // 2, -1, -1):
        found_any = False
        for combo in itertools.combinations_with_replacement(verts, k):
            b = dict(base); ok = True
            for v in combo:
                b[v] += 2
                if b[v] > H.degree(v):
                    ok = False; break
            if not ok:
                continue
            found_any = True
            if orc.query(H, b, -1, -1, 0, 0) == 1:
                return 1
        if found_any:
            return 0
    return 0


def run(graphs, outname, tag):
    stats = collections.Counter()
    fails = open(outname, 'w')
    for g6 in graphs:
        J = relabel(nx.from_graph6_bytes(g6))
        ev = even_vertices(J)
        if len(ev) != 2 or not J.has_edge(*ev):
            continue
        n = J.number_of_nodes()
        conn = nx.node_connectivity(J)
        c3 = conn >= 3
        for z, r in (ev, ev[::-1]):
            mc = has_matching_cut_fast(J.subgraph(set(J) - {z})) if c3 else None
            classes = ['all'] + (['3c'] if c3 else []) + (['3c_nomc'] if c3 and not mc else [])
            p0 = {v: J.degree(v) % 2 for v in J}
            p2 = dict(p0); p2[r] = 2
            ex0 = orc.query(J, p0, z, r, 0, 99)
            s0 = orc.query(J, p0, z, r, 1, 0)
            s2 = orc.query(J, p2, z, r, 1, 0) if not s0 else 1
            stl2 = int(s0 or s2)
            bal2 = 1 if stl2 else int(orc.query(J, p0, z, r, 0, 0) or orc.query(J, p2, z, r, 0, 0))
            for c in classes:
                stats[(c, 'inst')] += 1
                stats[(c, 'P0')] += ex0
                stats[(c, 'S0')] += s0
                stats[(c, 'STL2')] += stl2
                stats[(c, 'BAL2')] += bal2
            if not stl2 or not bal2:
                t2 = test2(J, z, r)
                rec = dict(g6=g6.decode(), n=n, z=z, r=r, dz=J.degree(z), dr=J.degree(r), conn=conn, mc=mc,
                           P0=ex0, S0=s0, STL2=stl2, BAL2=bal2, T2=t2,
                           degN=sorted(J.degree(w) for w in J[z]))
                fails.write(json.dumps(rec) + '\n'); fails.flush()
                for c in classes:
                    stats[(c, 'T2fail')] += 1 - t2
                    stats[(c, 'STL2fail_T2ok')] += (1 - stl2) * t2
    fails.close()
    for c in ('all', '3c', '3c_nomc'):
        if stats[(c, 'inst')]:
            print(f"[{tag}] {c}: instances {stats[(c,'inst')]}, P0 {stats[(c,'P0')]}, S0 {stats[(c,'S0')]}, "
                  f"STL2 {stats[(c,'STL2')]}, BAL2 {stats[(c,'BAL2')]}, T2fail {stats[(c,'T2fail')]}, "
                  f"STL2fail-but-T2 {stats[(c,'STL2fail_T2ok')]}", flush=True)


if __name__ == '__main__':
    graphs = [l.strip() for l in open(sys.argv[1], 'rb') if l.strip()]
    run(graphs, sys.argv[2], sys.argv[1])
