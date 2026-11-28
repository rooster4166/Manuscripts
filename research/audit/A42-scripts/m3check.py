"""A42: m = 3 at order 8, recomputed with a42solve and a42lib.check (own code).
Instances: connected all-odd graphs of order 8, unordered triples of disjoint ordered pairs (c,a), c !~ a.
LN3: Q(c_t) avoids a_t for t = 1,2,3.  J3: for some {i,j} with c_i, c_j joined in F - {a_i, a_j}, a
decomposition with c_i, c_j the ends of one path avoiding a_i, a_j and Q(c_k) avoiding a_k."""
import sys, itertools, subprocess, collections
sys.path.insert(0, __import__('os').path.dirname(__file__))
from a42lib import g6dec, comp_of, check_qa
Q = []; meta = []; ninst = 0; edges_of = {}
for g in open('odd8c.g6'):
    g = g.strip(); n, adj = g6dec(g); edges_of[g] = sum(map(len, adj)) // 2
    P = [(c, a) for c in range(n) for a in range(n) if c != a and a not in adj[c]]
    for T in itertools.combinations(P, 3):
        if len({x for p in T for x in p}) < 6: continue
        key = g + ''.join(' A %d %d' % p for p in T); idx = ninst; ninst += 1
        Q.append(key); meta.append((idx, 'LN3', key))
        for i, j in ((0, 1), (0, 2), (1, 2)):
            (ci, ai), (cj, aj) = T[i], T[j]; ck, ak = T[3 - i - j]
            if cj in comp_of(adj, ci, {ai, aj}):
                Q.append('%s J %d %d A %d %d A %d %d A %d %d' % (g, ci, cj, ci, ai, cj, aj, ck, ak)); meta.append((idx, 'J3', key))
out = subprocess.run(['./a42solve', '-b', '200000000'], input='\n'.join(Q) + '\n', capture_output=True, text=True).stdout.split('\n')[:len(Q)]
inst = collections.defaultdict(dict); C = collections.Counter()
for q, a, (idx, kind, key) in zip(Q, out, meta):
    r = check_qa(q, a); C['answer_' + r.split()[0]] += 1
    d = inst[idx]; d['key'] = key
    if kind == 'LN3': d['LN3'] = r
    else:
        d['J3any'] = True; d['J3'] = d.get('J3', False) or r == 'OK'; d.setdefault('J3q', []).append((q, r))
for d in inst.values():
    C['inst'] += 1; C['LN3_' + d['LN3']] += 1; C['joint_choice'] += d.get('J3any', False); C['J3'] += d.get('J3', False)
fail = sorted(d['key'] for d in inst.values() if d.get('J3any') and not d['J3'])
ref = sorted(l.strip() for l in open(sys.argv[1]) if l.strip())
nq = sum(len(d['J3q']) for d in inst.values() if d.get('J3any') and not d['J3'])
print(dict(C))
print('J3 failures', len(fail), 'their J3 queries', nq, 'all UNSAT:', all(r == 'UNSAT' for d in inst.values() if d.get('J3any') and not d['J3'] for _, r in d['J3q']))
print('failure list equals data/m3_J3_failures_order8.txt:', fail == ref)
print('edge counts of failures:', sorted(collections.Counter(edges_of[k.split()[0]] for k in fail).items()))
print('instances without a joint choice:', sum(1 for d in inst.values() if not d.get('J3any')))
