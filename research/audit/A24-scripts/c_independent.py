"""A24 (c): fully independent re-run of E26(C) on the 68 no-walk PTM instances (mylib only).
For each instance (G - F as graph6, F = {a1b1, a2b2}), all 8 orientations (ab, short end a; xy,
short end x), every walk P = y..a (simple path avoiding b, x), every Lovász decomposition D0 of
the base graph M = ((G - ab) + l1 b) - xy - E(P) separating {x,y}, {a,l1}, {l1,y} (own
enumerator, separation enforced by a path veto), the second leaf l2 at y, the walk back by
FORCED Fan chains (own code; a chain that reaches the endless x is stuck), merging, and a final
check on G.  Records, per instance: closable at all; closable with Theorem 3.4's hypothesis at
every tight step; the least successful walk length over all orientations.
usage: python3 c_independent.py nowalk68.txt [early]
With "early": all (orientation, walk) pairs are tried in order of walk length and an instance is
left as soon as a success satisfying Theorem 3.4's hypothesis is found (minlen values are then
still exact; nsucc counts are partial).
"""
import sys, collections
import mylib as M

L1, L2 = 100, 101


def simple_paths(G, s, t, banned):
    out = []
    def rec(p, seen):
        v = p[-1]
        if v == t:
            out.append(tuple(p)); return
        for w in sorted(G[v]):
            if w in seen or w in banned:
                continue
            seen.add(w); p.append(w); rec(p, seen); p.pop(); seen.discard(w)
    rec([s], {s})
    return out


def sep_ok(P, pairs):
    S = set(P)
    return not any(p in S and q in S for p, q in pairs)


def pred_of(D, w, y):
    out = set()
    for i in M.paths_ending(D, y):
        P = M.orient_from(D[i], y)
        if w in P:
            k = P.index(w)
            if k >= 1:
                out.add(P[k - 1])
    return out


def merge(D, leaf, v):
    return [tuple(v if q == leaf else q for q in P) for P in D]


def terminal_path(D, p, q):
    for i, P in enumerate(D):
        if (P[0] == p and P[1] == q) or (P[-1] == p and P[-2] == q):
            return i
    return None


C = collections.Counter()
for line in open(sys.argv[1]):
    w = line.split()
    if not w or w[0] != 'NOBASE':
        continue
    g6s = w[1]; a1, b1, a2, b2 = map(int, w[2:6])
    G = M.addedge(M.g6(g6s), (a1, b1), (a2, b2))
    any_ok = False; any_hyp = False; minlen = None; minlen_hyp = None
    nsucc = 0; nsucc_hyp = 0
    early = len(sys.argv) > 2 and sys.argv[2] == 'early'
    jobs = []
    for (e, f) in (((a1, b1), (a2, b2)), ((a2, b2), (a1, b1))):
        for a, b in (e, e[::-1]):
            for x, y in (f, f[::-1]):
                for P in simple_paths(G, y, a, {b, x}):
                    jobs.append((len(P), a, b, x, y, P))
    jobs.sort(key=lambda j: j[0])
    for _, a, b, x, y, P in jobs:
                    if early and any_hyp:
                        break
                    K = M.addedge(M.deledge(G, (a, b)), (L1, b))
                    Mg = M.deledge(K, (x, y), *[(P[i], P[i + 1]) for i in range(len(P) - 1)])
                    pairs = [(x, y), (a, L1), (L1, y)]
                    bM = M.lov(Mg)
                    for D0 in M.decomps_pg(Mg, bM, path_ok=lambda Q: sep_ok(Q, pairs)):
                        # second leaf
                        i = M.paths_ending(D0, y)[0]
                        D = list(D0); D[i] = M.orient_from(D0[i], y)[::-1] + (L2,)
                        H2 = M.addedge(M.deledge(K, (x, y)), (L2, y))
                        hyp = True; ok = True
                        for s in range(len(P) - 1):
                            Ks = M.deledge(H2, *[(P[j], P[j + 1]) for j in range(s, len(P) - 1)])
                            tgt, src = P[s], P[s + 1]
                            if x in Ks[tgt]:
                                for yy in {src} | Ks[tgt]:
                                    if x in pred_of(D, tgt, yy):
                                        hyp = False
                            st, ch, ix = M.forced_chain(D, src, tgt)
                            if st != 'ok':
                                ok = False
                                if ch[-1] != x:
                                    C['STUCK-NOT-AT-x'] += 1
                                break
                            D = M.exec_chain(D, ch, ix, tgt)
                            Ks2 = M.addedge(Ks, (tgt, src))
                            if not M.verify(Ks2, D):
                                C['BAD-INTERMEDIATE'] += 1
                        if not ok:
                            C['walkback-stuck'] += 1
                            continue
                        D4 = merge(merge(D, L2, x), L1, a)
                        if not M.verify(G, D4, M.lov(G)):
                            C['merge-invalid'] += 1
                            continue
                        ia, ixx = terminal_path(D4, a, b), terminal_path(D4, x, y)
                        if ia is None or ixx is None or ia == ixx:
                            C['not-PTM'] += 1
                            continue
                        any_ok = True; nsucc += 1
                        L = len(P) - 1
                        minlen = L if minlen is None else min(minlen, L)
                        if hyp:
                            any_hyp = True; nsucc_hyp += 1
                            minlen_hyp = L if minlen_hyp is None else min(minlen_hyp, L)
                        else:
                            C['success-without-hyp'] += 1
    C['instances'] += 1
    C['closed' if any_ok else 'NOT CLOSED'] += 1
    C['closed with Thm 3.4 hypothesis' if any_hyp else 'no success satisfies Thm 3.4 hypothesis'] += 1
    C[('min successful walk length', minlen)] += 1
    C[('min walk length with Thm 3.4 hyp', minlen_hyp)] += 1
    print('INST', g6s, a1, b1, a2, b2, 'closed', any_ok, 'hyp', any_hyp, 'minlen', minlen,
          'minlen_hyp', minlen_hyp, 'nsucc', nsucc, 'nsucc_hyp', nsucc_hyp, flush=True)
for k, v in sorted(C.items(), key=str):
    print(k, v)
