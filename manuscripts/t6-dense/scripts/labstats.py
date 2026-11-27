"""labstats.py: for every root, the number of labellings (r in {y1,y2,y3}, x1y2, x2y3 in E(B))
that have an append base in the exact Lean form (E7, else E6), and the fraction among all.
usage: labstats.py BUDGET < graphs.g6"""
import sys
import networkx as nx
from dense import ENG, shape, labellings, base_query, run_walk

budget = int(sys.argv[1])
tot = {}
for line in sys.stdin:
    line = line.strip()
    if not line or line.startswith('#'):
        continue
    B = nx.from_graph6_bytes(line.encode())
    sh, _ = shape(B)
    st = tot.setdefault(sh, dict(roots=0, labs=0, base_E7=0, base_E6only=0, none=0, und=0,
                                 min_frac=1.0, bad=0))
    for r in range(6):
        st['roots'] += 1
        labs = labellings(B, r)
        good = 0
        for L in labs:
            st['labs'] += 1
            (s7, D7), = ENG.run([base_query(B, L, 'endT', 0, budget)])
            if s7 == 'OK':
                out, _ = run_walk(B, L, D7, 'endT')
                st['bad'] += out != 'OK'
                st['base_E7'] += 1
                good += 1
                continue
            (s6, D6), = ENG.run([base_query(B, L, 'leanE6', 0, budget)])
            if s6 == 'OK':
                out, info = run_walk(B, L, D6, 'leanE6')
                st['bad'] += (out != 'OK') or not info.get('static')
                st['base_E6only'] += 1
                good += 1
            elif s6 == 'NONE' and s7 == 'NONE':
                st['none'] += 1
            else:
                st['und'] += 1
        st['min_frac'] = min(st['min_frac'], good / max(1, len(labs)))
for sh, st in tot.items():
    print('LABSTATS', sh, ' '.join('%s=%s' % (k, round(v, 3) if isinstance(v, float) else v)
                                   for k, v in st.items()), flush=True)
