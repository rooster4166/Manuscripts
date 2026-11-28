"""cfrun.py -- AE and the deletion form CF, exhaustive over a graph list (ae session).

usage: python3 cfrun.py graphs.g6 ./aesolve ./aecheck LABEL
For every AE instance (K, c, g) (cfgen.py) runs three query families with aesolve:
  AE  : 'A c g'
  CF0 : 'A c g' + 'T w g' for every neighbour w of g with d(w) >= 3  (b(w) = 2 at all of them)
  CF1 : for each such w0, CF0 without 'T w0 g'                        (one zero, at w0)
Every SAT witness is re-checked by aecheck (query and answer lines in pairs).  Prints, per
number t = |N(g) ∩ N(c)| of common neighbours, the number of instances, AE successes, CF0
successes, and CF<=1 successes (CF0 or some CF1)."""
import sys, os, subprocess
from collections import defaultdict
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'ln', 'scripts'))
from lnlib import g6_decode
gfile, solver, checker, label = sys.argv[1:5]
inst = []
for line in open(gfile):
    g6 = line.strip()
    if not g6: continue
    n, adj = g6_decode(g6)
    ev = [v for v in range(n) if adj[v] and len(adj[v]) % 2 == 0]
    if len(ev) != 1: continue
    g = ev[0]
    seen = {g}; st = [g]
    while st:
        u = st.pop()
        for v in adj[u]:
            if v not in seen: seen.add(v); st.append(v)
    W = sorted(w for w in adj[g] if len(adj[w]) >= 3)
    for c in sorted(seen):
        if c != g and c not in adj[g] and len(adj[c]) % 2 == 1:
            inst.append((g6, c, g, W, len(adj[g] & adj[c])))
queries = []; owner = []
for i, (g6, c, g, W, t) in enumerate(inst):
    base = f'{g6} A {c} {g}'
    queries.append(base); owner.append((i, 'AE'))
    queries.append(base + ''.join(f' T {w} {g}' for w in W)); owner.append((i, 'CF0'))
    for w0 in W:
        queries.append(base + ''.join(f' T {w} {g}' for w in W if w != w0)); owner.append((i, 'CF1'))
inp = '\n'.join(queries) + '\n'
out = subprocess.run([solver, '-b', '200000000'], input=inp, capture_output=True, text=True).stdout.splitlines()
assert len(out) == len(queries)
chk = subprocess.run([checker], input=''.join(q + '\n' + a + '\n' for q, a in zip(queries, out)),
                     capture_output=True, text=True)
ok = defaultdict(set)
und = 0
for (i, kind), a in zip(owner, out):
    if a.startswith('SAT'): ok[i].add(kind)
    elif a.startswith('UNDEC'): und += 1
stat = defaultdict(lambda: [0, 0, 0, 0])
for i, (g6, c, g, W, t) in enumerate(inst):
    s = stat[t]; s[0] += 1
    if 'AE' in ok[i]: s[1] += 1
    if 'CF0' in ok[i]: s[2] += 1
    if 'CF0' in ok[i] or 'CF1' in ok[i]: s[3] += 1
print(f'{label}: {len(inst)} instances, {len(queries)} queries, undecided {und}; checker: {chk.stdout.strip()}')
for t in sorted(stat):
    s = stat[t]
    print(f'  common neighbours t = {t}: instances {s[0]}, AE {s[1]}, CF0 (no zero) {s[2]}, CF<=1 (at most one zero) {s[3]}')
fails = [inst[i] for i in range(len(inst)) if 'CF0' not in ok[i] and 'CF1' not in ok[i]]
for f in fails[:20]: print('  CF<=1 FAIL', f[0], 'c', f[1], 'g', f[2])
sys.stdout.flush()
