"""partial.py: C4, canonical labellings.  Search bases satisfying only the L1*-admissible
conditions (E1' = P_y2, P_y3 avoid z; E2; E3; E4; E5), with several random orders, and report how
often the found base also satisfies E1 (z-path avoids x1) and E7 (P_x1 avoids y2) or E6.
usage: partial.py SEEDS BUDGET < graphs.g6"""
import sys
import networkx as nx
from dense import ENG, labellings, base_query, shape
from walksim import ends_count
seeds, budget = int(sys.argv[1]), int(sys.argv[2])
cnt = dict(bases=0, E1=0, E7=0, E1E7=0)
for line in sys.stdin:
    B = nx.from_graph6_bytes(line.strip().encode())
    if shape(B)[0] != 'C4':
        continue
    nB = B.number_of_nodes(); l1 = nB
    for r in range(4):
        for L in labellings(B, r):
            x1, y1, x2, y2, x3, y3 = (L[k] for k in ('x1', 'y1', 'x2', 'y2', 'x3', 'y3'))
            if B.has_edge(x2, y2) or B.has_edge(x3, y3) or B.has_edge(y2, y3):
                continue          # canonical: x2 y2 y3 x3 along the cycle
            qs = []
            for s in range(seeds):
                q = base_query(B, L, 'endA', s, budget)
                q['ef'] = {y2: [x2, l1], y3: [x3, l1], x2: [y3]}
                q['ep'] = [(y2, y3)]
                q.pop('es', None)
                qs.append(q)
            for st, D0 in ENG.run(qs):
                if st != 'OK':
                    continue
                cnt['bases'] += 1
                P = [P for P in D0 if l1 in P][0]
                e1 = x1 not in P
                Px1 = [Q for Q in D0 if Q[0] == x1 or Q[-1] == x1][0]
                e7 = y2 not in Px1
                cnt['E1'] += e1; cnt['E7'] += e7; cnt['E1E7'] += e1 and e7
print('PARTIAL', cnt)
