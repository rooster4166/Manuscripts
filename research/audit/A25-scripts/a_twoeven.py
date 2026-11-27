"""a_twoeven.py: the 476 bad (blocked instance, target) pairs with d(c) = 1 of out/badtargets9.txt,
classified against the 'two-even core' of section 5 ('d(c) = 1 with neighbour y, and y has no
neighbour in N(g)': then Q_c = cy is forced).  For the CHILD (G - gu, c, A), whose even vertex is u,
Q_c = cy is forced iff y has no neighbour outside A + {c}; the two even vertices of (G - gu) - c are
then y and u, and the two-even conjecture of L1S (Conj. 3.2) applies only at distance >= 3.
usage: python3 -I a_twoeven.py OUTDIR"""
import sys, collections
import networkx as nx
def sset(s):
    s = s.strip('{}'); return set(int(x) for x in s.split(',')) if s else set()
C = collections.Counter()
for l in open(sys.argv[1] + '/badtargets9.txt'):
    if not l.startswith('BADT'): continue
    p = l.split(); G = nx.from_graph6_bytes(p[1].encode())
    g, c, u = int(p[2][2:]), int(p[3][2:]), int(p[4][2:]); A = sset(p[5][2:])
    if G.degree(c) != 1: continue
    C['d(c)=1 bad targets'] += 1
    y = next(iter(G[c]))
    if u == y: C['target u = y (the neighbour of c)'] += 1; continue
    H = G.copy(); H.remove_edge(g, u)
    forced = all(z in A or z == c for z in H[y])
    if not forced: C['u != y, Q_c = cy not forced in the child'] += 1; continue
    K = H.copy(); K.remove_node(c)
    try: d = nx.shortest_path_length(K, y, u)
    except nx.NetworkXNoPath: d = 99
    C['u != y, Q_c = cy forced, dist_(G-gu-c)(y,u) = %s' % (d if d < 3 else '>=3')] += 1
    C['  of these: y in N(g) (in G)'] += y in G[g]
for k in sorted(C): print(k, C[k])
