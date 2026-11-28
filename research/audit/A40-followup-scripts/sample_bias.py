"""sample_bias.py ALLODD_G6 SAMPLE -- distribution of the order-10 sample of sample10.py.
sample10.py redraws the GRAPH when a quadruple is rejected, so a graph is drawn with probability
proportional to its number of admissible ordered quadruples (c1,a1,c2,a2): distinct, c1!~a1, c2!~a2.
Compares the mean edge count of the sample with the graph-uniform and the quadruple-weighted means."""
import sys, math
def dec(s):
    n = ord(s[0]) - 63; bits = []
    for ch in s[1:]:
        v = ord(ch) - 63; bits += [(v >> k) & 1 for k in range(5, -1, -1)]
    adj = [set() for _ in range(n)]; k = 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]: adj[i].add(j); adj[j].add(i)
            k += 1
    return n, adj
def quads(n, adj):
    c = 0
    for c1 in range(n):
        for a1 in range(n):
            if a1 == c1 or a1 in adj[c1]: continue
            for c2 in range(n):
                if c2 in (c1, a1): continue
                c += sum(1 for a2 in range(n) if a2 not in (c1, a1, c2) and a2 not in adj[c2])
    return c
gs = open(sys.argv[1]).read().split()
samp = [l.split()[0] for l in open(sys.argv[2]) if l.strip()]
st = {}
for g in gs:
    n, adj = dec(g); st[g] = (sum(len(a) for a in adj) // 2, quads(n, adj))
N = len(gs); mu = sum(st[g][0] for g in gs) / N
sd = math.sqrt(sum((st[g][0] - mu) ** 2 for g in gs) / N)
W = sum(st[g][1] for g in gs); muw = sum(st[g][0] * st[g][1] for g in gs) / W
sdw = math.sqrt(sum((st[g][0] - muw) ** 2 * st[g][1] for g in gs) / W)
ms = sum(st[g][0] for g in samp) / len(samp)
print('graphs %d, sample %d (distinct %d), graphs with no admissible quadruple %d' % (N, len(samp), len(set(samp)), sum(1 for g in gs if st[g][1] == 0)))
print('mean edges: graph-uniform %.3f (sd %.2f), quadruple-weighted %.3f (sd %.2f), sample %.3f' % (mu, sd, muw, sdw, ms))
print('z-score of the sample mean: vs graph-uniform %.1f, vs quadruple-weighted %.1f' % ((ms - mu) / (sd / math.sqrt(len(samp))), (ms - muw) / (sdw / math.sqrt(len(samp)))))
