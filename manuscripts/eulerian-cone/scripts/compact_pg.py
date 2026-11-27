"""compact_pg.py IN OUT: per-graph table from re.c output (decide or UC mode, all roots in order).

Each output line: graph6, then one digit per root (the size of the verified witness; 'x' if none),
then one letter per root: U (UC holds), O (RE holds; decide mode, or UC not shown), K (RE holds, UC
undecided within the budget), F (failure), ? (unknown).
"""
import sys

code = {"UC": "U", "OK": "O", "OKUNK": "K", "FAIL": "F", "UNK": "?"}
cur, sizes, stats = None, [], []
with open(sys.argv[1]) as f, open(sys.argv[2], "w") as g:
    def flush():
        if cur is not None:
            g.write("%s %s %s\n" % (cur, "".join(sizes), "".join(stats)))
    for line in f:
        g6, rest = line.split(None, 1)
        h = rest.split("|")[0].split()
        if g6 != cur:
            flush()
            cur, sizes, stats = g6, [], []
        sizes.append(h[1] if int(h[1]) >= 0 else "x")
        stats.append(code[h[3]])
    flush()
