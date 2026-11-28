"""Order 8: decide every non-weak pair (x ~ y, component of y in G - x inside N(x)) with my own
solver; Theorem 1.4 says all are bad. Prints running totals per graph (graphs in input order)."""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import indep
tot = bad = 0
for k, line in enumerate(sys.stdin):
    G = indep.read_g6(line)
    if any(len(G[v]) % 2 == 0 for v in G):
        continue
    t0 = time.time()
    seen = {}
    for y in G:
        for x in sorted(G[y]):
            if indep.weak(G, y, {x}):
                continue
            tot += 1
            g = indep.good(G, y, {x})
            bad += (not g)
            if g:
                print("THEOREM 1.4 VIOLATED?", line.strip(), y, x, flush=True)
    print(line.strip(), "nonweak so far", tot, "bad", bad, "%.1fs" % (time.time() - t0), flush=True)
print("TOTAL nonweak", tot, "bad", bad, flush=True)
