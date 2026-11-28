#!/usr/bin/env python3
"""Audit A39b: evaluate the hypotheses of the Lean statements literally at order 9.

For every degree-(n-2) root r of every J in J9_d6.g6 (B = J - z, k = 4) this enumerates every path Q
of G = B - r (any length) whose ends are neighbours of r, and evaluates:

  lean0(Q): hypotheses of `exists_decomp_of_connector` (delta = 0):
            src, tgt ~ r; every vertex of Q adjacent to r is an end; every x ~ r is odd in G - E(Q);
            lam = sum_{v in V(Q)} (d_{G'}(v) + 1) // 2; for 3 <= t <= k-1:
            ht // 2 + [t <= lam] + t <= k+1  or  h(t+1) // 2 + [t <= lam] + 2t <= k+1,
            ht = #{x ~ r, x notin V(Q), 2t <= d_B(x)}.
  lean1(Q): hypotheses of `exists_decomp_of_connector_mid` (delta = 1): as above but with exactly one
            further vertex y ~ r on Q, and (ht + 1) // 2.

It reports: the number of roots with s in Z; how many admit a Lean-delta=0 connector, a
Lean-delta=1 connector, the union; the length distribution of admissible connectors (the Lean
hypotheses force length <= 2 for delta = 0 and <= 3 for delta = 1); the roots reached only via a
length-3 connector (outside Theorem 4.1 as stated); and a comparison with the paper's formula
(Theorem 4.1, length 1 or 2 only).  It also prints one delta = 0 instance with lam >= 3 and
2 <= h~_3 <= 3 (a non-trivial t = 3 instance) for the Lean spine check.

Graph6 parsing is done here (no networkx).
"""
import sys
from collections import Counter

def g6(line):
    s = line.strip().split()[0]
    data = [ord(c) - 63 for c in s]
    n = data[0]; bits = []
    for d in data[1:]:
        for i in range(5, -1, -1): bits.append((d >> i) & 1)
    adj = [set() for _ in range(n)]; p = 0
    for j in range(1, n):
        for i in range(j):
            if bits[p]: adj[i].add(j); adj[j].add(i)
            p += 1
    return n, adj

def paths_between_N(G, N, maxlen):
    """All simple paths (as vertex lists) of the graph G (dict v->set) with both ends in N,
    length 1..maxlen, each unordered path once (src < tgt)."""
    out = []
    def ext(p):
        if len(p) - 1 >= 1 and p[-1] in N and p[0] < p[-1]:
            out.append(list(p))
        if len(p) - 1 == maxlen: return
        for w in G[p[-1]]:
            if w not in p: p.append(w); ext(p); p.pop()
    for a in N: ext([a])
    return out

def main(fn):
    roots = 0; sinZ = 0
    cnt = Counter(); lens = Counter(); only3 = 0; mism = 0
    example = None
    for line in open(fn):
        n, J = g6(line); k = (n - 1) // 2
        ev = [v for v in range(n) if len(J[v]) % 2 == 0]
        z = ev[0]; Z = set(J[z])
        V = [v for v in range(n) if v != z]
        B = {v: set(J[v]) - {z} for v in V}
        dB = {v: len(B[v]) for v in V}
        for r in sorted(Z):
            if len(J[r]) != n - 2: continue
            roots += 1
            N = set(B[r]); s = [v for v in V if v != r and v not in N][0]
            if s not in Z: continue
            sinZ += 1
            G = {v: set(B[v]) - {r} for v in V if v != r}
            ok0 = ok1 = False; ok_paper = False; ok_len_le2 = False
            # maxlen 7 covers every path of G (7 vertices); the hypotheses then cut it down
            for Q in paths_between_N(G, N, 7):
                EQ = {frozenset(e) for e in zip(Q, Q[1:])}
                dGp = {v: len(G[v]) - sum(1 for e in EQ if v in e) for v in G}
                if any(dGp[x] % 2 == 0 for x in N): continue          # hodd
                inner = [v for v in Q[1:-1] if v in N]
                if len(inner) > 1: continue
                delta = len(inner)
                lam = sum((dGp[v] + 1) // 2 for v in Q)
                Nt = [x for x in N if x not in Q]
                h = lambda t: sum(1 for x in Nt if 2 * t <= dB[x])
                good = all(
                    (h(t) + delta) // 2 + (1 if t <= lam else 0) + t <= k + 1 or
                    (h(t + 1) + delta) // 2 + (1 if t <= lam else 0) + 2 * t <= k + 1
                    for t in range(3, k))
                lens[(delta, len(Q) - 1, good)] += 1
                if good:
                    if delta == 0: ok0 = True
                    else: ok1 = True
                    if len(Q) - 1 <= 2: ok_len_le2 = True
                    if delta == 0 and lam >= 3 and 2 <= h(3) <= 3 and example is None:
                        example = (line.split()[0], z, r, s, Q, lam, h(3))
                # the paper's Theorem 4.1 condition (length 1 or 2), written from the tex
                if len(Q) - 1 <= 2:
                    dpap = 1 if (len(Q) == 3 and Q[1] in N) else 0
                    gp = all(
                        (h(t) + dpap) // 2 + (1 if lam >= t else 0) + t <= k + 1 or
                        (h(t + 1) + dpap) // 2 + (1 if lam >= t else 0) + 2 * t <= k + 1
                        for t in range(3, k))
                    if gp != good: mism += 1
                    if gp: ok_paper = True
            cnt[('lean0', ok0)] += 1; cnt[('lean1', ok1)] += 1
            cnt[('lean0|lean1', ok0 or ok1)] += 1
            cnt[('paper len<=2', ok_paper)] += 1
            cnt[('lean, some len<=2 connector', ok_len_le2)] += 1
            if (ok0 or ok1) and not ok_len_le2: only3 += 1
    print('degree-(n-2) roots:', roots, ' with s in Z:', sinZ)
    for kk in sorted(cnt): print(kk, cnt[kk])
    print('connectors passing hodd + hQint, by (delta, length, condition holds):')
    for kk in sorted(lens): print('  ', kk, lens[kk])
    print('roots reached by Lean only through a length-3 connector:', only3)
    print('paper-vs-Lean condition mismatches on length<=2 connectors:', mism)
    print('non-trivial delta=0 example (g6, z, r, s, Q, lam, h3):', example)

if __name__ == '__main__':
    main(sys.argv[1])
