"""closure.py: is the N2 class closed under the proved transfer moves? (session claude/dl-one)

Instance (G, c, A): G at most one even vertex g, c odd, A disjoint from N[c] (A may contain g).
Class K: some w in N(c), w != g, with N(w) & A <= {g}.
Moves (transfers proved unconditionally, l1-induction Thm 3.1):
 (a) g even, c in N(g):            (G - gc, g, A+{c})
 (b) g even, x in N(g)-A-N[c]:     (G - gx, c, A)
 (c) g even, x in N(g)&N(c)-A:     (G - xc - gx, x, A+{c})
 (d) no even vertex, d(c) >= 3, y in N(c)-A: (G - cy + y l, l, A+{c})
 (i) boundary: C = component of c in G - A; (G, c, N(C)) if smaller
Base: A misses the component of c;  no even vertex and d(c) = 1 (neighbour not in A);
      no even vertex and |A| = 1 (L1, lovasz_avoid_nonadj).
Reports instances of K with no move into K or base.
usage: closure.py N [maxA]
"""
import sys
import itertools
import subprocess
from collections import Counter

def graphs(n):
    out = subprocess.run(["nauty-geng", "-cq", str(n)], capture_output=True, text=True).stdout
    for line in out.split():
        yield line

def g6(s):
    n = ord(s[0]) - 63
    bits = []
    for ch in s[1:]:
        v = ord(ch) - 63
        bits += [(v >> k) & 1 for k in range(5, -1, -1)]
    A = {i: set() for i in range(n)}
    p = 0
    for j in range(1, n):
        for i in range(j):
            if bits[p]:
                A[i].add(j); A[j].add(i)
            p += 1
    return A

def copyg(G):
    return {v: set(N) for v, N in G.items()}

def even(G):
    ev = [v for v in G if len(G[v]) > 0 and len(G[v]) % 2 == 0]
    return ev

def comp(G, v):
    seen = {v}; st = [v]
    while st:
        x = st.pop()
        for y in G[x]:
            if y not in seen:
                seen.add(y); st.append(y)
    return seen

def in_K(G, c, A):
    ev = even(G)
    if len(ev) > 1 or len(G[c]) % 2 == 0 or c in A:
        return False
    g = ev[0] if ev else None
    if A & (G[c] | {c}):
        return False
    for w in G[c]:
        if w == g:
            continue
        if (G[w] & A) <= ({g} if g is not None else set()):
            return True
    return False

def base(G, c, A):
    A = {a for a in A if G[a]}
    if not (A & comp(G, c)):
        return True
    ev = even(G)
    if not ev:
        if len(G[c]) == 1 and not (G[c] & A):
            return True
        if len(A) == 1 and not (A & (G[c] | {c})):
            return True
    return False

def children(G, c, A):
    ev = even(G)
    g = ev[0] if ev else None
    res = []
    if g is not None:
        if c in G[g]:
            H = copyg(G); H[g].discard(c); H[c].discard(g)
            res.append(("a", H, g, A | {c}))
        for x in G[g]:
            if x in A or x == c:
                continue
            if x not in G[c]:
                H = copyg(G); H[g].discard(x); H[x].discard(g)
                res.append(("b%d" % x, H, c, set(A)))
            else:
                H = copyg(G); H[g].discard(x); H[x].discard(g); H[x].discard(c); H[c].discard(x)
                res.append(("c%d" % x, H, x, A | {c}))
    else:
        if len(G[c]) >= 3:
            for y in G[c]:
                if y in A:
                    continue
                H = copyg(G); l = max(H) + 1
                H[c].discard(y); H[y].discard(c); H[y].add(l); H[l] = {y}
                res.append(("d%d" % y, H, l, A | {c}))
    # boundary
    rest = {v for v in G if v not in A}
    seen = {c}; st = [c]
    while st:
        x = st.pop()
        for y in G[x]:
            if y in rest and y not in seen:
                seen.add(y); st.append(y)
    bd = set()
    for x in seen:
        bd |= G[x] & A
    if bd != A:
        res.append(("i", G, c, bd))
    return res

def main():
    n = int(sys.argv[1])
    maxA = int(sys.argv[2]) if len(sys.argv) > 2 else 99
    C = Counter()
    for s in graphs(n):
        G = g6(s)
        ev = even(G)
        if len(ev) > 1:
            continue
        g = ev[0] if ev else None
        for c in G:
            if len(G[c]) % 2 == 0:
                continue
            cand = [v for v in G if v != c and v not in G[c]]
            for k in range(1, min(maxA, len(cand)) + 1):
                for A in itertools.combinations(cand, k):
                    A = set(A)
                    if not in_K(G, c, A):
                        continue
                    C["inK"] += 1
                    if base(G, c, A):
                        C["base"] += 1
                        continue
                    ok = [m for (m, H, c2, A2) in children(G, c, A) if in_K(H, c2, A2) or base(H, c2, A2)]
                    if ok:
                        C["moved"] += 1
                        C["first_" + ok[0][0]] += 1
                    else:
                        C["STUCK"] += 1
                        if C["STUCK"] <= 15:
                            print("STUCK", s, "g=%s c=%d A=%s" % (g, c, sorted(A)),
                                  "N(c)=%s" % sorted(G[c]), "N(g)=%s" % (sorted(G[g]) if g is not None else "-"), flush=True)
    print(dict(C))

main()
