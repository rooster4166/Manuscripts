"""jall.py -- Conjecture J, exhaustive over a list of all-odd graphs.

For every graph (graph6 on the input file) and every instance (unordered pair of disjoint ordered
pairs (c1,a1),(c2,a2) with c_i not adjacent to a_i):
  * if c1, c2 lie in one component of F - {a1, a2}: query 'J c1 c2 A c1 a1 A c2 a2' (a Lovasz
    decomposition in which c1, c2 are the two ends of one path avoiding a1 and a2);
  * otherwise the instance is 'separated' and is written out for the separated-case run.
Each chunk is solved by SOLVER (budget B nodes), every SAT witness is checked by CHECKER (wcheck,
independent code), and the non-SAT queries are rerun with budget 100*B.
usage: jall.py GRAPHS SOLVER CHECKER B OUTPREFIX"""
import sys, subprocess, os
from multiprocessing import Pool
import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'ln', 'scripts'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lnlib import g6_decode

GR, SOLVER, CHECKER, B, OUT = sys.argv[1:6]

def instances(g):
    n, adj = g6_decode(g)
    P = [(c, a) for c in range(n) for a in range(n) if c != a and a not in adj[c]]
    J, sep = [], []
    for i, (c1, a1) in enumerate(P):
        for (c2, a2) in P[i + 1:]:
            if len({c1, a1, c2, a2}) < 4: continue
            seen = {c1}; st = [c1]
            while st:
                u = st.pop()
                for v in adj[u]:
                    if v not in seen and v != a1 and v != a2: seen.add(v); st.append(v)
            if c2 in seen: J.append('%s J %d %d A %d %d A %d %d' % (g, c1, c2, c1, a1, c2, a2))
            else: sep.append('%s %d %d %d %d' % (g, c1, a1, c2, a2))
    return J, sep

def solve(Q, budget):
    out = subprocess.run([SOLVER, '-b', str(budget)], input='\n'.join(Q) + '\n',
                         capture_output=True, text=True).stdout.split('\n')[:len(Q)]
    chk = subprocess.run([CHECKER], input=''.join(q + '\n' + a + '\n' for q, a in zip(Q, out)),
                         capture_output=True, text=True).stdout
    return out, chk

def work(graphs):
    Q, S = [], []
    for g in graphs:
        J, sep = instances(g); Q += J; S += sep
    out, chk = solve(Q, int(B))
    fails = [l for l in chk.split('\n') if l.startswith(('FAIL', 'BAD', 'MISMATCH', 'NOWIT'))]
    last = [l for l in chk.split('\n') if l.startswith('witnesses')][0]
    nsat = int(last.split()[2].rstrip(','))
    rest = [q for q, a in zip(Q, out) if not a.startswith('SAT')]
    nsat2 = 0; rest2 = []
    if rest:
        out2, chk2 = solve(rest, 100 * int(B))
        fails += [l for l in chk2.split('\n') if l.startswith(('FAIL', 'BAD', 'MISMATCH', 'NOWIT'))]
        last2 = [l for l in chk2.split('\n') if l.startswith('witnesses')][0]
        nsat2 = int(last2.split()[2].rstrip(','))
        rest2 = [q + ' -> ' + a.split()[0] for q, a in zip(rest, out2) if not a.startswith('SAT')]
    return len(Q), nsat, nsat2, rest2, fails, S

if __name__ == '__main__':
    G = [l.strip() for l in open(GR) if l.strip()]
    chunks = [G[i:i + 40] for i in range(0, len(G), 40)]
    tot = sat = sat2 = 0; nsep = 0
    fo = open(OUT + '.nonsat', 'w'); ff = open(OUT + '.fail', 'w'); fs = open(OUT + '.sep', 'w')
    with Pool(4) as pool:
        for k, (q, s1, s2, rest2, fails, S) in enumerate(pool.imap_unordered(work, chunks)):
            tot += q; sat += s1; sat2 += s2; nsep += len(S)
            for l in rest2: fo.write(l + '\n')
            for l in fails: ff.write(l + '\n')
            for l in S: fs.write(l + '\n')
            fo.flush(); ff.flush(); fs.flush()
            if k % 20 == 0:
                print('chunks %d/%d  J-queries %d  SAT %d (+%d on rerun)  separated %d' %
                      (k + 1, len(chunks), tot, sat, sat2, nsep), flush=True)
    print('DONE graphs %d  J-queries %d  SAT(checked) %d + %d  non-SAT %d  separated %d' %
          (len(G), tot, sat, sat2, tot - sat - sat2, nsep), flush=True)
