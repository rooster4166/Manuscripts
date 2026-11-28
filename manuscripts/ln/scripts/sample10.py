"""sample10.py ALLODD_G6 -- the order-10 sample of L_N(2) instances (seed 11).

ALLODD_G6 lists the connected graphs of order 10 with all degrees odd, in nauty order:
    nauty-geng -cq 10 | ./allodd_filter > allodd10.g6        (32,851 graphs)
Output: 3000 lines "g6 c1 a1 c2 a2": a graph drawn uniformly, then four distinct vertices drawn
uniformly, rejected if c1 ~ a1 or c2 ~ a2.  This reproduces data/order10_sample_instances.txt."""
import random, sys
from lnlib import g6_decode
rng = random.Random(11)
gs = open(sys.argv[1]).read().split()
out = []
while len(out) < 3000:
    g = rng.choice(gs); n, adj = g6_decode(g)
    c1, a1, c2, a2 = rng.sample(range(n), 4)
    if a1 in adj[c1] or a2 in adj[c2]: continue
    out.append('%s %d %d %d %d' % (g, c1, a1, c2, a2))
print('\n'.join(out))
