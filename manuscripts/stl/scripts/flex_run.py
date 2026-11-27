"""E22 (D): how rigid is STL?  On 3-connected J with unique even vertex z:
  EE(u)   : some Lovasz D has u short (uz terminal at u)            [multi-sep's EE]
  STS(u)  : some star-terminal Lovasz D has u short
  HALF(S) : some star-terminal Lovasz D has short set exactly S      (every half-set S of N(z))
  PAIR(M) : some star-terminal Lovasz D has transition pairing M     (every perfect matching M of N(z))
usage: flex_run.py graphs.g6|jsonl out.jsonl [max_graphs] [budget] [3c|zc]
"""
import sys, json, itertools, collections
import networkx as nx
from common import Oracle, even_vertices, relabel, has_matching_cut_fast
from brute_flex import pairings

orc = Oracle()
src = sys.argv[1]; out = open(sys.argv[2], 'w')
maxg = int(sys.argv[3]) if len(sys.argv) > 3 else 10 ** 9
budget = int(sys.argv[4]) if len(sys.argv) > 4 else 0
cls = sys.argv[5] if len(sys.argv) > 5 else '3c'   # '3c': J 3-connected; 'zc': J - z connected
if src.endswith('.jsonl'):
    g6s = [json.loads(l)['g6'].encode() for l in open(src)]
else:
    g6s = [l.strip() for l in open(src, 'rb') if l.strip()]
stats = collections.Counter(); ng = 0


def q(*a, **k):
    if budget:
        k.setdefault('seed', 1); k.setdefault('budget', budget)
    return orc.query(*a, **k)


for g6 in g6s:
    J = relabel(nx.from_graph6_bytes(g6))
    ev = even_vertices(J)
    if len(ev) != 1:
        continue
    if cls == '3c' and nx.node_connectivity(J) < 3:
        continue
    if cls == 'zc' and not nx.is_connected(J.subgraph(set(J) - {ev[0]})):
        continue
    ng += 1
    if ng > maxg:
        break
    z = ev[0]; N = sorted(J[z]); k = len(N) // 2
    prof = {v: J.degree(v) % 2 for v in J}
    mc = has_matching_cut_fast(J.subgraph(set(J) - {z}))
    rec = dict(g6=g6.decode(), n=J.number_of_nodes(), dz=len(N), mc=mc)
    rec['EE'] = {u: q(J, prof, z, -1, 0, 99, req={u: z}) for u in N}
    rec['STS'] = {u: q(J, prof, z, -1, 1, 99, req={u: z}) for u in N}
    hs = {}
    for S in itertools.combinations(N, k):
        req = {x: z for x in S}; forb = {y: z for y in N if y not in S}
        hs[' '.join(map(str, S))] = q(J, prof, z, -1, 1, 99, req=req, forb=forb)
    rec['HALF'] = hs
    pm = {}
    for M in pairings(N):
        pairs = {}
        for a, b in M:
            pairs[a] = {b}; pairs[b] = {a}
        pm[' '.join(f'{a}-{b}' for a, b in M)] = q(J, prof, z, -1, 1, 99, pairs=pairs)
    rec['PAIR'] = pm
    out.write(json.dumps(rec) + '\n'); out.flush()
    stats['graphs'] += 1
    stats['EE_all'] += all(v == 1 for v in rec['EE'].values())
    stats['STS_all'] += all(v == 1 for v in rec['STS'].values())
    stats['HALF_all'] += all(v == 1 for v in hs.values())
    stats['PAIR_all'] += all(v == 1 for v in pm.values())
    stats['EE_pairs'] += len(N); stats['EE_ok'] += sum(v == 1 for v in rec['EE'].values())
    stats['STS_ok'] += sum(v == 1 for v in rec['STS'].values())
    stats['HALF_n'] += len(hs); stats['HALF_ok'] += sum(v == 1 for v in hs.values())
    stats['PAIR_n'] += len(pm); stats['PAIR_ok'] += sum(v == 1 for v in pm.values())
    stats['undecided'] += sum(v == 2 for d in (rec['EE'], rec['STS'], hs, pm) for v in d.values())
print('FLEX', src, dict(stats), flush=True)
