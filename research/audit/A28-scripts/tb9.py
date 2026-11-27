"""A28: triangle base (Lean form: every root with data has some base) on TM's order-9 list
d6_9.g6 (lines = B = J - z, the even vertices of B are N(z)).  Witnesses are verified here:
D0 must partition E(M) into simple paths with ends = deg_M mod 2 and satisfy (2.1)."""
import itertools, subprocess, sys
import networkx as nx

ORACLE, FILE, BUD = sys.argv[1], sys.argv[2], int(sys.argv[3])

def pms(vs, J):
    if not vs:
        yield []; return
    a = vs[0]
    for b in vs[1:]:
        if J.has_edge(a, b):
            for pm in pms([v for v in vs[1:] if v != b], J):
                yield [(a, b)] + pm

def verify_base(M, n, pairs, paths):
    used = set(); ends = [0] * n
    for P in paths:
        assert len(P) >= 2 and len(set(P)) == len(P)
        for x, y in zip(P, P[1:]):
            e = frozenset((x, y)); assert M.has_edge(x, y) and e not in used; used.add(e)
        ends[P[0]] += 1; ends[P[-1]] += 1
    assert len(used) == M.number_of_edges()
    assert all(ends[v] == M.degree(v) % 2 for v in range(n))
    Q = {}
    for P in paths:
        Q[P[0]] = P; Q[P[-1]] = P
    for a, b in pairs:
        assert (a not in Q[b]) or (b not in Q[a]), (a, b)

def shape(J, U):
    D = nx.complement(J.subgraph(U))
    m = D.number_of_edges(); degs = sorted(d for _, d in D.degree())
    if m == 0: return 'empty'
    if m == 1: return 'K2'
    if m == 2 and degs[-1] == 2: return 'P3'
    if m == 3 and degs[-3:] == [2, 2, 2]: return 'K3'
    if m == 4 and degs[-4:] == [2, 2, 2, 2] and nx.is_connected(D.subgraph([v for v in D if D.degree(v)])): return 'C4'
    return 'other'

st = dict(graphs=0, roots=0, nodata=0, found=0, absent=0, undec=0, queries=0, q2=0, verified=0)
byshape = {}
for line in open(FILE):
    line = line.strip()
    if not line: continue
    B = nx.from_graph6_bytes(line.encode())
    nb = B.number_of_nodes(); n = nb + 1
    J = nx.relabel_nodes(B, {v: v + 1 for v in B})
    U = [v for v in J if J.degree(v) % 2 == 0]
    assert len(U) == 6
    for u in U: J.add_edge(0, u)
    assert all(J.degree(v) % 2 == 1 for v in J if v != 0) and J.degree(0) == 6
    st['graphs'] += 1
    sh = shape(J, U); byshape.setdefault(sh, [0, 0, 0])
    for r in sorted(U):
        st['roots'] += 1
        verdict = None; anyund = False; havedata = False
        for w in sorted(U):
            if w == r: continue
            rest = [u for u in sorted(U) if u not in (r, w)]
            for pairs in pms(rest, J):
                havedata = True
                M = J.copy(); M.remove_edges_from([(0, w)] + [(0, x) for p in pairs for x in p] + pairs)
                E = list(M.edges()); b = [M.degree(v) % 2 for v in range(n)]
                qs = []
                for cb in itertools.product([0, 1], repeat=len(pairs)):
                    xs = [0] * n
                    for (a, c), o in zip(pairs, cb):
                        if o == 0: xs[c] |= 1 << a
                        else: xs[a] |= 1 << c
                    qs.append("WAB %d %d %s %s %s 5 %d" % (n, len(E), " ".join("%d %d" % e for e in E),
                              " ".join(map(str, b)), " ".join(map(str, xs)), BUD))
                p = subprocess.run([ORACLE], input="\n".join(qs) + "\n", capture_output=True, text=True)
                out = p.stdout.strip().split("\n"); assert len(out) == len(qs)
                st['queries'] += len(out); st['q2'] += sum(o.startswith('2') for o in out)
                for o in out:
                    if o.startswith('1'):
                        paths = [list(map(int, s.split())) for s in o.split('|')[1:] if s.strip()]
                        verify_base(M, n, pairs, paths); st['verified'] += 1
                        verdict = 'FOUND'; break
                if verdict: break
                if any(o.startswith('2') for o in out): anyund = True
            if verdict: break
        if not havedata: st['nodata'] += 1; continue
        if verdict == 'FOUND': st['found'] += 1; byshape[sh][0] += 1
        elif anyund: st['undec'] += 1; byshape[sh][1] += 1; print('UNDEC', line, 'r', r, flush=True)
        else: st['absent'] += 1; byshape[sh][2] += 1; print('ABSENT', line, 'r', r, flush=True)
print('FINAL', st); print('byshape [found, undec, absent]', byshape)
