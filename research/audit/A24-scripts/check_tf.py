"""A24 (d): cross-check tf.py (the authors' enumerator and Fan routine) against the independent
mylib.py on all connected graphs of small order.

1. Enumeration: for every connected graph of order n (geng -c), for the Lovász end counts and
   for up to R random feasible end-count vectors b, the multiset of canonical decompositions
   from tf.decomps equals that from mylib.decomps_pg (path growing).  Also with the authors'
   pruning (c, avoid) and (c, region) against post-filtering of the full list.
2. Fan: for every graph with at most one even vertex g and every u in N(g), every Lovász
   decomposition D' of G - gu: tf.fan_moves(D', g, u) gives exactly one result, equal to the
   result of mylib's forced chain executed per RD Lemma 2.2, and equal to the set of results
   of mylib.all_fan_results (all chains, general definition).
usage: python3 check_tf.py TFDIR nmax [R] [nmin] [fanonly]
(fanonly: skip the random-b and pruning checks; Lovász b enumeration and the Fan check only)
"""
import sys, subprocess, random, collections
sys.path.insert(0, sys.argv[1])
import tf
import mylib as M

nmax = int(sys.argv[2]); R = int(sys.argv[3]) if len(sys.argv) > 3 else 2
random.seed(7)
C = collections.Counter()


def tfg(G):
    return {v: set(G[v]) for v in G}


nmin = int(sys.argv[4]) if len(sys.argv) > 4 else 3
fanonly = len(sys.argv) > 5 and sys.argv[5] == 'fanonly'
for n in range(nmin, nmax + 1):
    gs = subprocess.run(['nauty-geng', '-cq', str(n)], capture_output=True, text=True).stdout.split()
    for s in gs:
        G = M.g6(s)
        bs = [M.lov(G)]
        for _ in range(0 if fanonly else R):
            # random feasible b: b(v) = d(v) mod 2 + 2*r, r random small, total even automatically
            b = {v: (len(G[v]) % 2) + 2 * random.randint(0, max(0, (len(G[v]) - len(G[v]) % 2) // 2))
                 for v in G}
            bs.append(b)
        for b in bs:
            mine = collections.Counter(M.canon(D) for D in M.decomps_pg(G, b))
            theirs = collections.Counter(M.canon([tuple(P) for P in D]) for D in tf.decomps(tfg(G), b))
            C['enum-cases'] += 1
            C['enum-decomps'] += sum(mine.values())
            if mine != theirs:
                C['ENUM-MISMATCH'] += 1
                print("ENUM MISMATCH", s, b, sum(mine.values()), sum(theirs.values()), flush=True)
            if any(v > 1 for v in mine.values()):
                C['MINE-DUPLICATES'] += 1
            for D in mine:
                assert M.verify(G, list(D), b)
        # pruning: Lovász b, each odd c, random A, and region
        b = M.lov(G)
        allD = [list(D) for D in M.decomps_pg(G, b)]
        for c in (G if not fanonly else []):
            if b[c] != 1:
                continue
            A = frozenset(v for v in G if v != c and random.random() < 0.35)
            Rg = frozenset([c] + [v for v in G if v != c and random.random() < 0.6])
            exp_av = collections.Counter(M.canon(D) for D in allD
                                         if not (set(M.path_with_end(D, c)) & A))
            exp_rg = collections.Counter(M.canon(D) for D in allD
                                         if set(M.path_with_end(D, c)) <= Rg)
            got_av = collections.Counter(M.canon([tuple(P) for P in D])
                                         for D in tf.decomps(tfg(G), b, c, A))
            got_rg = collections.Counter(M.canon([tuple(P) for P in D])
                                         for D in tf.decomps(tfg(G), b, c, region=Rg))
            C['prune-cases'] += 2
            if exp_av != got_av:
                C['PRUNE-AVOID-MISMATCH'] += 1; print("AVOID MISMATCH", s, c, sorted(A), flush=True)
            if exp_rg != got_rg:
                C['PRUNE-REGION-MISMATCH'] += 1; print("REGION MISMATCH", s, c, sorted(Rg), flush=True)
        # Fan
        ev = M.evens(G)
        if len(ev) > 1:
            continue
        if len(ev) == 0:
            continue
        g = ev[0]
        for u in sorted(G[g]):
            G1 = M.deledge(G, (g, u)); b1 = M.lov(G1)
            for D1 in M.decomps_pg(G1, b1):
                st, ch, ix = M.forced_chain(D1, g, u)
                assert st == 'ok'  # Z(u) empty: Fan's inequality 1 > 0
                mineD = M.exec_chain(D1, ch, ix, u)
                assert M.verify(G, mineD, M.lov(G))
                # vertex-set property
                allr = M.all_fan_results(D1, g, u)
                tfr = tf.fan_moves([tuple(P) for P in D1], g, u)
                tfset = set(M.canon([tuple(P) for P in D2]) for D2, _, _ in tfr)
                C['fan-cases'] += 1
                if len(tfr) != 1:
                    C['TF-FAN-NOT-ONE-RESULT'] += 1
                if tfset != {M.canon(mineD)} or allr != {M.canon(mineD)}:
                    C['FAN-MISMATCH'] += 1
                    print("FAN MISMATCH", s, g, u, D1, flush=True)
                # tf chain sequence equals mine
                if tfr and tuple(tfr[0][1]) != tuple(ch):
                    C['CHAIN-SEQ-MISMATCH'] += 1
    print("n", n, dict(C), flush=True)
print("SUMMARY", dict(C))
