"""A24 (a): independent re-derivation of E26(A) at order n (default 7): blocked L1* residuals,
every good Lovász decomposition D' of G - gu, the forced Fan chain g -> u, and the dichotomy
"result good iff the forced chain avoids c".  Uses only mylib.py (own graph6 decoder, own
path-growing enumerator, own chain).  Instance filter re-implemented from l1star Def. 4.1,
Lemma 5.1 (A = boundary of C) and Corollary 5.6 items 1-6.

Also: Theorem 3.2's hypothesis (no vertex of {g} + N(u) has c as predecessor of u in the leaf
graph D3 = D' with Q_c extended by a leaf), the leaf-graph forced chain (Theorem 2.2 /
Corollary 2.3), uniqueness of the Fan image over all chains, and where the chain meets c.

usage: python3 a_dichotomy.py n K|max [limit_instances] [stride] [offset] [cap]
cap: at most cap good D' per target (default unlimited); a per-instance line is flushed.
tlim (argv[7]): seconds per target (default unlimited); a target that runs out is recorded as TIMEOUT
and its partial counts are kept.
"""
import sys, subprocess, itertools, collections
import mylib as M

n = int(sys.argv[1]); mode = sys.argv[2]
lim = int(sys.argv[3]) if len(sys.argv) > 3 else 10 ** 9
stride = int(sys.argv[4]) if len(sys.argv) > 4 else 1
offset = int(sys.argv[5]) if len(sys.argv) > 5 else 0
cap = int(sys.argv[6]) if len(sys.argv) > 6 else 10 ** 12
tlim = int(sys.argv[7]) if len(sys.argv) > 7 else 0
import signal
class _TO(Exception):
    pass
def _alarm(sig, frm):
    raise _TO()
signal.signal(signal.SIGALRM, _alarm)
amax = (mode == 'max'); K = 0 if amax else int(mode)
LEAF = 'L'


def comp_of(G, c, removed):
    seen = {c}; q = [c]
    for x in q:
        for y in G[x]:
            if y not in seen and y not in removed:
                seen.add(y); q.append(y)
    return seen


def instances():
    gs = subprocess.run(['nauty-geng', '-cq', str(n)], capture_output=True, text=True).stdout.split()
    for s in gs:
        G = M.g6(s)
        ev = M.evens(G)
        if len(ev) != 1:
            continue
        g = ev[0]; Ng = G[g]
        for c in G:
            if len(G[c]) % 2 == 0 or c in Ng:
                continue
            cand = [v for v in G if v != c and v not in G[c] and v not in Ng]
            if amax:
                sets = [tuple(cand)]
            else:
                sets = [S for k in range(1, K + 1) for S in itertools.combinations(cand, k)]
            for S in sets:
                A = frozenset(S)
                if not A:
                    continue
                C = comp_of(G, c, A)
                if any(not (G[a] & C) for a in A):
                    continue                      # A != boundary of C (Lemma 5.1)
                if any(not (G[u] & (A - {g})) for u in Ng):
                    continue                      # not blocked
                irr = True
                if not amax:
                    irr = irreducible(G, g, c, A, C)
                yield s, G, g, c, A, irr


def irreducible(G, g, c, A, C):
    Ng = G[g]; Nc = G[c]
    if g not in A and g in C:
        return False                              # Cor 5.6(3), Prop 5.2
    allowed = set(G) - A - {c, g}
    if len(Nc) != 1:
        allowed -= Nc
    R = comp_of({v: G[v] for v in G}, g, set(G) - allowed - {g})
    for z in R - {g}:
        if not (G[z] & A):
            return False                          # Cor 5.6(4), Prop 5.3
    if len(Ng) == 2:
        u, v = sorted(Ng)
        if v in G[u]:
            if g in A:
                return False                      # Prop 5.4(ii)
        else:
            if g not in A or u not in Nc or v not in Nc:
                return False                      # Prop 5.4(i)
    if len(Nc) == 3:
        for y1, y2 in itertools.permutations(sorted(Nc), 2):
            if y2 not in G[y1] and y1 not in Ng:
                return False                      # Prop 5.5
    return True


def qc(D, c):
    return M.path_with_end(D, c)


C = collections.Counter(); EX = []
ninst = 0
for idx, (s, G, g, c, A, irr) in enumerate(instances()):
    if not irr:
        continue
    ninst += 1
    if ninst > lim:
        break
    if (ninst - 1) % stride != offset:
        continue
    typ = ("gA" if g in A else "sep", "d(g)=%d" % len(G[g]))
    C[typ + ('instances',)] += 1
    goodu = []; inst_sc = False; tight_inst = False
    for u in sorted(G[g]):
        G1 = M.deledge(G, (g, u)); b1 = M.lov(G1)
        assert len(G1[c]) % 2 == 1
        ngood = 0
        cedges = [(c, y) for y in sorted(G1[c])]
        okf = (lambda P, A=A: not ((P[0] == c or P[-1] == c) and (set(P) & A)))
        if tlim:
            signal.alarm(tlim)
        try:
          for D1 in M.decomps_pg(G1, b1, first_edges=cedges, path_ok=okf):
              if set(qc(D1, c)) & A:
                  raise AssertionError('pruning failed')
              ngood += 1
              if ngood > cap:
                  C['CAPPED-targets'] += 1
                  break
              st, ch, ix = M.forced_chain(D1, g, u)
              assert st == 'ok'
              D2 = M.exec_chain(D1, ch, ix, u)
              assert M.verify(G, D2, M.lov(G))
              res_good = not (set(qc(D2, c)) & A)
              thru = c in ch
              inNc = u in G[c]
              C[typ + (inNc, thru, res_good)] += 1
              if n <= 7:
                  allr = M.all_fan_results(D1, g, u)
                  if allr != {M.canon(D2)}:
                      C['FAN-IMAGE-NOT-UNIQUE'] += 1
              if thru:
                  i = ch.index(c)
                  Qprev = D1[ix[i - 1]]
                  C[('thru-c', 'step', i, 'Q_{i-1} contains g', g in Qprev,
                     'Q_{i-1} meets A', bool(set(Qprev) & A))] += 1
                  if res_good and len(EX) < 10:
                      EX.append((s, g, c, sorted(A), u, D1, ch))
              if inNc:
                  tight_inst = True
                  # Theorem 3.2 hypothesis in the leaf graph D3
                  i = M.paths_ending(D1, c)[0]
                  D3 = list(D1); D3[i] = M.orient_from(D1[i], c)[::-1] + (LEAF,)
                  srcs = [g] + sorted(G1[u])
                  sc = True
                  for y in srcs:
                      for j in M.paths_ending(D3, y):
                          P = M.orient_from(D3[j], y)
                          if u in P:
                              k = P.index(u)
                              if k >= 1 and P[k - 1] == c:
                                  sc = False
                  st3, ch3, ix3 = M.forced_chain(D3, g, u)
                  C[typ + ('tight', 'SC' if sc else 'noSC', 'leafchain-' + st3,
                           'plainthru' if thru else 'plainavoid', res_good)] += 1
                  if sc:
                      inst_sc = True
                      assert st3 == 'ok' and res_good
                  # Corollary 2.3(1): leaf chain stuck iff it reaches c iff plain chain passes c
                  if (st3 == 'stuck') != thru:
                      C['COR2.3-LEAF-VS-PLAIN-DIFFER'] += 1
                  if st3 == 'stuck' and ch3[-1] != c:
                      C['STUCK-NOT-AT-c'] += 1
        except _TO:
            C['TIMEOUT-targets'] += 1
        finally:
            signal.alarm(0)
        if ngood:
            goodu.append(u)
    C[typ + ('good-u', 'outside-N(c)' if any(u not in G[c] for u in goodu)
             else ('only-in-N(c)' if goodu else 'NONE'))] += 1
    if tight_inst:
        C[typ + ('tight-instance', "SC-some-D'" if inst_sc else 'no-SC')] += 1
    print('INST', ninst, s, g, c, sorted(A), typ, 'goodu', goodu, 'thru-good-so-far', len(EX), flush=True)
    if ninst % 100 == 1:
        print('PARTIAL', sorted(((str(k), v) for k, v in C.items())), flush=True)
print("order", n, "mode", mode, "irreducible blocked instances processed", sum(v for k, v in C.items() if k[-1:] == ('instances',)))
print("key = (type, d(g), u in N(c), chain passes c, result good)")
for k, v in sorted(C.items(), key=str):
    print(k, v)
for e in EX:
    print("EX-thru-c-but-good", e)
