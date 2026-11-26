# Written by an independent internal referee agent (Nov 2026); copied here for reproducibility.
"""Compare direct extension search with (UH)&(LH) over all B, WITHOUT the |U| bound
(and also allowing p_i up to the Thm B bounds only), on exhaustive small decompositions.
Tests both directions of Prop. cuts + Lemma flow-record + Cor. record."""
import itertools, sys
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from thmB_exhaustive import decomps, extension_exists

def comps_of(m, edges):
    adj = {v: [] for v in range(m)}
    for u, v in edges: adj[u].append(v); adj[v].append(u)
    seen = set(); out = []
    for v in range(m):
        if v in seen or len(adj[v]) == 2: continue
        if not adj[v]: seen.add(v); out.append((v, v)); continue
        prev, cur = None, v; seen.add(v)
        while True:
            nx_ = [w for w in adj[cur] if w != prev]
            if not nx_: break
            prev, cur = cur, nx_[0]; seen.add(cur)
        out.append((v, cur))
    return out

def cuts_ok(m, n, E, colv, c, delta):
    kap = [2 if i == c else 4 for i in range(n)]
    CS = [comps_of(m, [e for e, j in zip(E, colv) if j == i]) for i in range(n)]
    for bits in range(1 << m):
        B = {v for v in range(m) if bits >> v & 1}
        uh = 0; lh = 0
        for i in range(n):
            n1 = n2 = 0
            for (u, w) in CS[i]:
                sl = (u in B) + (w in B)  # trivial: u==w gives 0 or 2
                if sl == 1: n1 += 1
                elif sl == 2: n2 += 1
            psi = n1 + n2 + (1 if (i != c and n2 >= 1) else 0)
            uh += min(kap[i], psi)
            lh += max(0, delta[i] - psi)
        if 2*len(B) > uh: return False, 'UH', B
        if lh > 2*(m - len(B)): return False, 'LH', B
    return True, None, None

def main(n, m):
    k = 2*n + 1 - m
    E, D = decomps(m, n)
    tot = agree = infeas = 0; mism = []; failtypes = {}
    seen = set()
    for colv in D:
        p = [m - sum(1 for j in colv if j == i) for i in range(n)]
        if max(p) > k: continue
        for usz in range(1, n+1):
            for U in itertools.combinations(range(n), usz):
                if any(p[i] > k-1 for i in U): continue
                for c in U:
                    T = [i for i in range(n) if i not in U]
                    key = tuple(sorted((('T' if i in T else ('c' if i == c else 'S')),
                                         tuple(sorted(e for e, j in zip(E, colv) if j == i))) for i in range(n)))
                    if key in seen: continue
                    seen.add(key)
                    delta = [0]*n
                    for i in range(n):
                        if i in T: delta[i] = max(0, p[i]+4-k)
                        elif i == c: delta[i] = max(0, p[i]+3-k)
                        else: delta[i] = max(0, p[i]+5-k)
                    d = extension_exists(m, n, E, colv, c, delta)
                    ok, typ, B = cuts_ok(m, n, E, colv, c, delta)
                    tot += 1; agree += (d == ok); infeas += (not d)
                    if not ok: failtypes[(typ, len(B) == 0, 2*len(U) <= k-2)] = failtypes.get((typ, len(B) == 0, 2*len(U) <= k-2), 0) + 1
                    if d != ok: mism.append((colv, U, c, d, typ, B))
    print(f"n={n} m={m} k={k}: inst={tot} agree={agree} infeasible={infeas} failtypes={failtypes} mism={mism[:3]}")

if __name__ == '__main__':
    main(int(sys.argv[1]), int(sys.argv[2]))
