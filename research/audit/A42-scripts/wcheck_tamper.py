"""A42: adversarial tests of wcheck.c.  (1) targeted corruptions, each violating one condition;
(2) random corruptions; in both, wcheck's verdict is compared with a42lib.check (own checker).
A disagreement where wcheck accepts and a42lib rejects is a hole in wcheck."""
import sys, random, subprocess
sys.path.insert(0, __import__('os').path.dirname(__file__))
from a42lib import parse_query, parse_answer, check
random.seed(17)
Q = [l.strip() for l in open(sys.argv[1]) if l.strip()]
A = [l.strip() for l in open(sys.argv[2])][:len(Q)]
def fmt(g, paths): return 'SAT %s :: ' % g + ' ; '.join('-'.join(map(str, P)) for P in paths)
cases = []   # (label, query, answer)
for q, a in list(zip(Q, A))[:3000]:
    st, paths = parse_answer(a)
    if st != 'SAT': continue
    g = q.split()[0]; n, adj, req, avoid, sep, join = parse_query(q)
    P = [list(p) for p in paths]
    kind = random.randrange(12)
    if kind == 0 and len(P) > 1:                         # drop a path
        i = random.randrange(len(P)); P2 = P[:i] + P[i + 1:]; lab = 'drop'
    elif kind == 1:                                       # duplicate a path
        P2 = P + [P[0]]; lab = 'dup'
    elif kind == 2:                                       # split a long path into two (changes ends)
        L = [p for p in P if len(p) >= 3]
        if not L: continue
        p = L[0]; k = random.randrange(1, len(p) - 1); P2 = [x for x in P if x is not p] + [p[:k + 1], p[k:]]; lab = 'split'
    elif kind == 3:                                       # join two paths sharing an end (may repeat vertices)
        pr = [(x, y) for x in P for y in P if x is not y and x[-1] == y[0]]
        if not pr: continue
        x, y = pr[0]; P2 = [z for z in P if z is not x and z is not y] + [x + y[1:]]; lab = 'join'
    elif kind == 4:                                       # make a path non-simple: append its first vertex
        p = P[0]; P2 = [p + [p[1]]] + P[1:]; lab = 'nonsimple'
    elif kind == 5:                                       # vertex out of range
        P2 = [P[0][:-1] + [n]] + P[1:]; lab = 'range'
    elif kind == 6:                                       # single-vertex path added
        P2 = P + [[P[0][0]]]; lab = 'single'
    elif kind == 7:                                       # rotate a path (non-edge or changes edges)
        p = P[0]
        if len(p) < 3: continue
        P2 = [p[1:] + p[:1]] + P[1:]; lab = 'rotate'
    elif kind == 8 and avoid:                             # move the avoided vertex onto the tail's path: swap labels in query
        t, x = avoid[0]
        cand = [v for p in P if p[0] == t or p[-1] == t for v in p if v != t]
        if not cand: continue
        q = q.replace('A %d %d' % (t, x), 'A %d %d' % (t, cand[0]), 1); P2 = P; lab = 'avoid'
    elif kind == 9 and join:                              # change the J pair in the query
        p0, p1 = join[0]; others = [v for v in range(n) if v not in (p0, p1)]
        q = q.replace('J %d %d' % (p0, p1), 'J %d %d' % (p0, random.choice(others)), 1); P2 = P; lab = 'Jpair'
    elif kind == 10:                                      # reverse a path (valid)
        P2 = [P[0][::-1]] + P[1:]; lab = 'reverse(valid)'
    else:                                                 # wrong graph name
        cases.append(('graph', q, a.replace(g, g[:-1] + chr(ord(g[-1]) ^ 1), 1))); continue
    cases.append((lab, q, fmt(g, P2)))
# also hand-made traps
g = 'E@UW'  # net: 23 14 34 05 35 45
cases += [('trap: empty witness', g + ' A 0 1', 'SAT E@UW ::'),
          ('trap: missing ::', g + ' A 0 1', 'SAT E@UW 0-5 ; 1-4-3-2 ; 3-5-4'),
          ('trap: valid', g + ' A 0 1', 'SAT E@UW :: 0-5 ; 1-4-3-2 ; 3-5-4'),
          ('trap: avoid on interior path', g + ' A 0 3', 'SAT E@UW :: 0-5-3 ; 1-4-3-2 ; 5-4'),
          ('trap: x-suffix garbage', g + ' A 0 1', 'SAT E@UW :: 0-5x ; 1-4-3-2 ; 3-5-4'),
          ('trap: extra blank paths', g + ' A 0 1', 'SAT E@UW :: 0-5 ; ; 1-4-3-2 ;; 3-5-4 ;'),
          ('trap: unknown query token', g + ' X 0 5', 'SAT E@UW :: 0-5 ; 1-4-3-2 ; 3-5-4'),
          ('trap: R makes 2 ends', g + ' R 4 2', 'SAT E@UW :: 0-5 ; 1-4-3-2 ; 3-5-4')]
inp = ''.join(q + '\n' + a + '\n' for _, q, a in cases)
# run wcheck one pair at a time to get per-case verdicts
holes = 0; agree = 0; import collections; C = collections.Counter()
for lab, q, a in cases:
    out = subprocess.run(['./wcheck'], input=q + '\n' + a + '\n', capture_output=True, text=True).stdout
    wacc = 'failures 0' in out and 'witnesses checked 1' in out
    try:
        st, paths = parse_answer(a)
        n, adj, req, avoid, sep, join = parse_query(q)
        mine = st == 'SAT' and q.split()[0] == a.split()[1] and check(n, adj, paths, req, avoid, sep, join) is None
    except Exception as e:
        mine = None
    C[(lab, 'wcheck accepts' if wacc else 'wcheck rejects', 'a42 accepts' if mine else ('a42 parse error' if mine is None else 'a42 rejects'))] += 1
    if wacc and not mine: holes += 1
for k in sorted(C): print(k, C[k])
print('cases', len(cases), 'wcheck accepts but own checker rejects:', holes)
