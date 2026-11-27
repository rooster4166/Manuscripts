"""Collect UND / RUND lines from ptm outputs and print them as ptm 'f' input (one instance per line).
RUND lines also carry the end; the f-mode re-run tests PTM and all ends anyway."""
import sys, glob
seen = set()
for fn in sys.argv[1:]:
    for line in open(fn):
        t = line.split()
        if not t or t[0] not in ('UND', 'RUND'): continue
        g6 = t[1]; pairs = [x.rstrip('*') for x in t[2:] if '-' in x and not x.startswith(('end', 'GF'))]
        key = (g6, tuple(pairs))
        if key in seen: continue
        seen.add(key)
        print(g6, ' '.join(p.replace('-', ' ') for p in pairs))
