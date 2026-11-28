"""table3_prop61.py (A36): Table 3 per row, from the authors' run files, with the roots that
Proposition 6.1 proves unscheduled (fewer than k = 2 non-neighbours) moved from 'undecided' to 'none'.
usage: table3_prop61.py DATA_DIR"""
import sys
import networkx as nx
d = sys.argv[1]
def verdicts(fn):
    v = {}
    for l in open(fn):
        if l.startswith('ROOT'):
            p = l.split(); v[(p[1], int(p[2][2:]))] = int(p[3][8:])
    return v
def shape(B):
    H = nx.complement(B.subgraph(range(6))); m = H.number_of_edges()
    degs = sorted(d for _, d in H.degree() if d)
    return {0: 'empty', 1: 'K2', 4: 'C4'}.get(m, 'P3' if degs == [1, 1, 2] else 'K3' if degs == [2, 2, 2] else str(sorted(H.edges())))
for fam, runs in (('resid_O8', 'resid_O8_s1_b2e6'), ('resid_O10', 'resid_O10_s1_b2e6'), ('e28_hard', 'e28_hard_s1_b2e6'),
                  ('clt_hard', 'clt_hard_s1_b2e6')):
    v = verdicts('%s/runs/%s.txt' % (d, runs))
    rows = {}
    for line in open('%s/%s.g6' % (d, fam)):
        g = line.split()[0]
        B = nx.from_graph6_bytes(g.encode()); n = B.number_of_nodes()
        J = B.copy(); J.add_edges_from((n, u) for u in range(6))
        key = (fam, shape(B) if fam.startswith('resid') else 'all', n + 1)
        R = rows.setdefault(key, [0, 0, 0, 0, 0])   # roots, sched, none, undec, undec-but-Prop6.1
        for r in range(6):
            if J.degree(r) < 3: continue
            ver = v[(g, r)]; t = sum(1 for x in J if x != r and not J.has_edge(r, x))
            R[0] += 1; R[1 + [1, 0, 2].index(ver)] += 1
            if ver == 2 and t < 2: R[4] += 1
            assert not (ver == 1 and t < 2), ('Prop 6.1 violated', g, r)
    for key, R in rows.items():
        print('%-10s %-6s |J|=%d roots %d sched %d none %d undec %d | Prop6.1 decides %d undecided -> none %d undec %d'
              % (key[0], key[1], key[2], R[0], R[1], R[2], R[3], R[4], R[2] + R[4], R[3] - R[4]))
