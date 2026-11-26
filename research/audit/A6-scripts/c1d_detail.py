import glob
from collections import Counter
rows = []; skips = 0
for f in sorted(glob.glob('c1d_[0-9]*.txt')):
    for l in open(f):
        if l.startswith('#'): skips += 1; continue
        rows.append(l.split())
graphs = {p[0] for p in rows}
print('graphs processed', len(graphs) + skips, 'six-even graphs', len(graphs), 'rooted instances', len(rows))
print('status', Counter(p[2] for p in rows))
print('tightness', Counter(p[5] for p in rows))
tight = [p for p in rows if p[5] == 'tight']
print('tight roots by (D-shape, RS-candidate):', sorted(Counter((p[3], p[4]) for p in tight).items()))
print('all roots by (D-shape, RS-candidate):', sorted(Counter((p[3], p[4]) for p in rows).items()))
print('graphs with a tight root:', len({p[0] for p in tight}))
