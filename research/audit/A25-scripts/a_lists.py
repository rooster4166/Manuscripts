"""a_lists.py: independent analysis (networkx only) of the authors' committed failure lists.
usage: python3 -I a_lists.py OUTDIR    (OUTDIR = manuscripts/l1-induction/scripts/out of the audited commit)
  * stprime9.txt (STPFAIL lines): the shape claims of section 4 after Prop. 4.7;
  * badtargets9.txt (BADT lines): the d(c)/d(g) split of section 5;
  * explore9_MBT.txt (STUCK lines with nch=0): "every neighbour of the even vertex is in A";
  * stuck0_9.txt: H?ABvrw minus its leaf versus G?Bvvo."""
import sys, re, collections
import networkx as nx

out = sys.argv[1]
def sset(s):
    s = s.strip('{}')
    return set(int(x) for x in s.split(',')) if s else set()

# ---- ST' failures
rows = []
for l in open(out + '/stprime9.txt'):
    if not l.startswith('STPFAIL'): continue
    p = l.split()
    G = nx.from_graph6_bytes(p[1].encode())
    g = int(p[2][2:]); c = int(p[3][2:]); A = sset(p[4][2:])
    rows.append((p[1], G, g, c, A))
C = collections.Counter()
for g6, G, g, c, A in rows:
    Ng, Nc = set(G[g]), set(G[c])
    C['total'] += 1
    C['N(g) in N(c)'] += Ng <= Nc
    C['d(g)=%d' % G.degree(g)] += 1
    if G.degree(g) == 2:
        u, v = sorted(Ng)
        C['d(g)=2, g in A'] += g in A
        C['d(g)=2, uv not edge'] += not G.has_edge(u, v)
        C['d(g)=2, g in A and uv not edge (L1S Cor 5.6(5) shape)'] += (g in A and not G.has_edge(u, v))
    if G.degree(g) == 4:
        C['d(g)=4, d(c)=%d' % G.degree(c)] += 1
    allin = all(set(G[u]) - {g, c} <= A for u in Ng)
    C['every target u: N(u)-{g,c} in A'] += allin
    if allin and all(G.degree(u) == 3 for u in Ng):
        C['... and every target of degree 3'] += 1
for k in sorted(C): print('STPFAIL', k, C[k])

# ---- bad targets
B = collections.Counter()
for l in open(out + '/badtargets9.txt'):
    if not l.startswith('BADT'): continue
    p = l.split(); G = nx.from_graph6_bytes(p[1].encode())
    g = int(p[2][2:]); c = int(p[3][2:])
    B['total'] += 1
    B['d(c)=%d d(g)=%d' % (G.degree(c), G.degree(g))] += 1
    if G.degree(c) == 1:
        y = next(iter(G[c]))
        B['d(c)=1, y in N(g)'] += y in G[g]
        B['d(c)=1, y has a neighbour in N(g)'] += any(z in G[g] for z in G[y])
for k in sorted(B): print('BADT', k, B[k])

# ---- explore9_MBT: stuck states with no move
E = collections.Counter()
for l in open(out + '/explore9_MBT.txt'):
    if not l.startswith('STUCK'): continue
    m = re.search(r'g=(-?\d+) c=(\d+) A=(\{[^}]*\}).*adm=(\d) nch=(\d+) E: (.*)$', l)
    g, c, A, adm, nch, es = int(m.group(1)), int(m.group(2)), sset(m.group(3)), int(m.group(4)), int(m.group(5)), m.group(6).split()
    G = nx.Graph(); G.add_edges_from(tuple(map(int, e.split('-'))) for e in es)
    E['stuck states'] += 1
    E['admissible'] += adm
    if nch == 0:
        E['nch=0'] += 1
        Ng = set(G[g]) if g in G else set()
        E['nch=0 and N(g)-{c} in A'] += (Ng - {c}) <= A
        E['nch=0 and N(g) in A'] += Ng <= A
        E['nch=0 and c in N(g)'] += c in Ng
for k in sorted(E): print('EXPLORE', k, E[k])

# ---- H?ABvrw minus the leaf 5 versus G?Bvvo
H = nx.from_graph6_bytes(b'H?ABvrw')
leaves = [v for v in H if H.degree(v) == 1]
H2 = H.copy(); H2.remove_nodes_from(leaves)
T = nx.from_graph6_bytes(b'G?Bvvo')
print('H?ABvrw leaves', leaves, 'leaf neighbour degree', [H.degree(next(iter(H[v]))) for v in leaves])
print('H?ABvrw - leaf isomorphic to G?Bvvo:', nx.is_isomorphic(H2, T))
print('G?Bvvo even vertices', [v for v in T if T.degree(v) % 2 == 0 and T.degree(v) > 0], 'degrees', dict(T.degree()))
