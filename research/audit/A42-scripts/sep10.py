"""A42: order-10 separated instances (sep10.txt from instclass.c): (1) AE queries for the leaf-at-head
instances not covered by B or by G without the NA clause; (2) the Criterion R set (neither B, nor G
without NA, nor leaf) compared with data/separated10_criterionR.txt, and every certificate's static
conditions (Def 3.3: P a path of F from c_i avoiding a_i, ending outside {c_j, a_j}) checked, plus an
exact query 'F - E(P) + c_j l, S l a_j' for Lemma R(b) per certificate."""
import sys
sys.path.insert(0, __import__('os').path.dirname(__file__))
from a42lib import g6dec, g6enc, comp_of
def corB(adj, c1, a1, c2, a2):
    if any(a1 in adj[x] and a2 in adj[x] for x in range(len(adj))): return False
    for ci, ai in ((c1, a1), (c2, a2)):
        if len(adj[ci]) == 1:
            w = next(iter(adj[ci]))
            if ai != w and ai not in adj[w]: return True
    return False
def glue_noNA(adj, ci, ai, cj, aj):
    v = aj; B = comp_of(adj, cj, {v})
    if ci in B: return False
    return ai not in B or len(adj[v] & B) % 2 == 1 or ci not in adj[v]
aeq = open('AE10.q', 'w'); crset = set(); nae = 0
for l in open('sep10.txt'):
    t = l.split(); g = t[0]; n, adj = g6dec(g); c1, a1, c2, a2 = map(int, t[1:5])
    if corB(adj, c1, a1, c2, a2) or glue_noNA(adj, c1, a1, c2, a2) or glue_noNA(adj, c2, a2, c1, a1): continue
    leaf = None
    for ci, ai, cj, aj in ((c1, a1, c2, a2), (c2, a2, c1, a1)):
        if len(adj[ci]) == 1 and aj in adj[ci]: leaf = (ci, ai, cj, aj); break
    if leaf:
        ci, ai, cj, aj = leaf; A = [set(s) for s in adj]; A[ci].discard(aj); A[aj].discard(ci)
        aeq.write('%s A %d %d\n' % (g6enc(n, A), cj, aj)); nae += 1
    else: crset.add(' '.join(t[:5]))
aeq.close()
print('AE queries', nae, 'Criterion R set', len(crset))
cert = {}; bad = 0; rq = open('CR10.q', 'w')
for l in open(sys.argv[1]):
    t = l.split(); key = ' '.join(t[2:7]); P = [int(x) for x in t[7][2:].split('-')]
    cert[key] = (t[1], P)
    g = t[2]; n, adj = g6dec(g); c1, a1, c2, a2 = map(int, t[3:7])
    ok = all(b in adj[a] for a, b in zip(P, P[1:])) and len(set(P)) == len(P) and len(P) >= 2
    if P[0] == c1: ci, ai, cj, aj = c1, a1, c2, a2
    elif P[0] == c2: ci, ai, cj, aj = c2, a2, c1, a1
    else: ok = False; ci = None
    if ok: ok = ai not in P and P[-1] not in (cj, aj) and t[1] == 'pre'
    if not ok: bad += 1; print('BAD CERT', l.strip()); continue
    A = [set(s) for s in adj]
    for p, q in zip(P, P[1:]): A[p].discard(q); A[q].discard(p)
    A.append({cj}); A[cj].add(n); rq.write('%s S %d %d\n' % (g6enc(n + 1, A), n, aj))
rq.close()
print('certificates', len(cert), 'statically bad', bad, 'set equal to Criterion R set:', set(cert) == crset)
