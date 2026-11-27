"""A29: every orientation certified by dlrec must hold according to the exact solver.
usage: python3 cert_sound.py ori579.txt pairs579.txt"""
import sys
cert = {}
for line in open(sys.argv[1]):
    if line.startswith('ORI'):
        _, g6, a, b, r1, r2 = line.split(); cert[(g6, int(a), int(b))] = (int(r1), int(r2))
dl = {}
for line in open(sys.argv[2]):
    p = line.split(';'); g6 = p[0].strip()
    for item in p[2].split(','):
        f = item.split()
        if len(f) >= 5:
            a, b, ob, oa, tw = map(int, f[:5]); dl[(g6, a, b)] = (ob, oa)
bad = sum(1 for k, (r1, r2) in cert.items() if (r1 and not dl[k][0]) or (r2 and not dl[k][1]))
print("pairs", len(cert), "certified orientations", sum(r1 + r2 for r1, r2 in cert.values()), "UNSOUND", bad)
