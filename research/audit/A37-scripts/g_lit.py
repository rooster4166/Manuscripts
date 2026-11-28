"""g_lit.py (audit A37, item 3g): recount the Pyber / Fan conditions of Corollary 3.3 with my own
code (no networkx).  K = J[N(z) - r] (the E-subgraph of B = J - z, which I re-derive from the
degrees of B rather than assume).  Pyber: K is a forest.  Fan: every block of K (maximal
2-connected induced subgraph on >= 3 vertices, or a bridge) is triangle-free with maximum degree
<= 3 inside the block.  SEMI: e(B) > 2k^2.
usage: python3 g_lit.py FILE [gz]
"""
import gzip
import itertools
import sys
from collections import Counter

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from a37lib import adjacency, connected_without, delete_vertex, g6_decode


def two_connected(S, A):
    S = set(S)
    sub = {v: A[v] & S for v in S}
    vs = sorted(S)
    idx = {v: i for i, v in enumerate(vs)}
    Aloc = [set(idx[w] for w in sub[v]) for v in vs]
    n = len(vs)
    if not connected_without(n, Aloc, set()):
        return False
    return all(connected_without(n, Aloc, {i}) for i in range(n))


def blocks(Vk, A):
    Vk = sorted(Vk)
    big = []
    for s in range(len(Vk), 2, -1):
        for S in itertools.combinations(Vk, s):
            S = frozenset(S)
            if any(S <= T for T in big):
                continue
            if two_connected(S, A):
                big.append(S)
    out = list(big)
    for a, b in itertools.combinations(Vk, 2):
        if b in A[a] and not any({a, b} <= T for T in big):
            out.append(frozenset((a, b)))
    return out


def main():
    fn = sys.argv[1]
    op = gzip.open if fn.endswith(".gz") else open
    st = Counter()
    with op(fn, "rt") as fh:
        for line in fh:
            g6, z, r = line.split()[:3]
            z, r = int(z), int(r)
            n, E = g6_decode(g6)
            A = adjacency(n, E)
            B = delete_vertex(E, z)
            AB = adjacency(n, B)
            evB = {v for v in range(n) if v != z and len(AB[v]) % 2 == 0}
            assert evB == set(A[z]) - {r}          # Lemma 1.2: even vertices of B = N(z) - r
            Vk = evB
            Ak = [AB[v] & Vk if v in Vk else set() for v in range(n)]
            ek = sum(len(Ak[v]) for v in Vk) // 2
            # forest: edges = vertices - components
            comps, seen = 0, set()
            for v in Vk:
                if v in seen:
                    continue
                comps += 1
                stck = [v]
                seen.add(v)
                while stck:
                    u = stck.pop()
                    for w in Ak[u]:
                        if w not in seen:
                            seen.add(w)
                            stck.append(w)
            pyber = ek == len(Vk) - comps
            fan = True
            for Bl in blocks(Vk, Ak):
                degs = [len(Ak[v] & Bl) for v in Bl]
                tri = any(b in Ak[a] and c in Ak[a] and c in Ak[b] for a, b, c in itertools.combinations(sorted(Bl), 3))
                if max(degs) > 3 or tri:
                    fan = False
            k = (n - 2) // 2
            semi = len(B) > 2 * k * k
            d = len(A[z])
            st[("inst", d)] += 1
            st[("PYBER", d)] += pyber
            st[("FAN", d)] += fan
            st[("SEMI", d)] += semi
            st[("neither", d)] += (not fan) and (not semi)
            if d == 4:
                tri3 = ek == 3
                st[("d4: Fan fails <=> triangle", (not fan) == tri3)] += 1
            if pyber and not fan:
                st["PYBER but not FAN (impossible)"] += 1
    for kk in sorted(st, key=str):
        print(kk, st[kk])


if __name__ == "__main__":
    main()
