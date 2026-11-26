import glob
from collections import Counter
rows = []; skips = 0; done = len(glob.glob('c1d_*.done'))
for f in glob.glob('c1d_[0-9]*.txt'):
    for l in open(f):
        if l.startswith('#'): skips += 1; continue
        p = l.split()
        rows.append(p)
graphs = {p[0] for p in rows}
print('slices done', done, '/6; graphs processed', len(graphs) + skips, '/ 11117; six-even graphs', len(graphs), '; rooted instances', len(rows))
print('status', Counter(p[2] for p in rows))
print('fails', [p for p in rows if p[2] != 'pass'][:10])
print('shape/candidate distribution', sorted(Counter((p[3], p[4]) for p in rows).items()))
