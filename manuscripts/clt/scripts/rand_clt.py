"""rand_clt.py: random tests of constrained-Lovász statements (session claude/clt).

usage: python3 rand_clt.py FORM N TRIALS SEED [BUDGET] [K]

Random connected graphs on N vertices with at most one even vertex (parity repaired by toggling
pairs of even vertices), random density.  For each graph, a random system of the given FORM with
up to K tails (default 4) is built in its *maximal* form and decided exactly by lsearch.c.

FORMS
  bip1     tails C (odd, distinct), every vertex h outside N[C] u N(g) assigned to one tail
           phi(h) uniformly at random; constraint: Q_c avoids phi^{-1}(c)  (the CLT_1 form)
  bip1u    as bip1, but assignment by nearest tail (ties random)
  star     one tail, A = V - (N[c] u N(g))   (L1* local form; control)
  lnmatch  disjoint arcs c_i -> a_i with a_i not in N[c_i] u N(g)  (L_N with an even vertex)
  bip1ne   bip1 plus: the end paths of the tails are pairwise distinct
  bipx     CLT-B: every vertex h outside N(g) u C is assigned to a random tail c with h not in N[c]
           (heads may be adjacent to other tails); graphs whose even vertex has degree 2 are
           redrawn
Prints one line per failure and a summary.
"""
import sys
import random
from clt_lib import solve_many, check, to_g6


def rand_graph(n, rng):
    while True:
        p = rng.uniform(2.2 / n, 0.75)
        adj = [set() for _ in range(n)]
        for i in range(n):
            for j in range(i + 1, n):
                if rng.random() < p:
                    adj[i].add(j)
                    adj[j].add(i)
        # repair parity: toggle edges between pairs of even vertices
        for _ in range(4 * n):
            ev = [v for v in range(n) if len(adj[v]) % 2 == 0]
            if len(ev) <= 1:
                break
            a, b = rng.sample(ev, 2)
            if b in adj[a]:
                adj[a].discard(b)
                adj[b].discard(a)
            else:
                adj[a].add(b)
                adj[b].add(a)
        ev = [v for v in range(n) if len(adj[v]) % 2 == 0]
        if len(ev) > 1 or any(not adj[v] for v in range(n)):
            continue
        seen = {0}
        st = [0]
        while st:
            x = st.pop()
            for y in adj[x]:
                if y not in seen:
                    seen.add(y)
                    st.append(y)
        if len(seen) == n:
            return adj


def bfs(n, adj, src):
    d = [99] * n
    d[src] = 0
    q = [src]
    for x in q:
        for y in adj[x]:
            if d[y] == 99:
                d[y] = d[x] + 1
                q.append(y)
    return d


def build(form, n, adj, rng, K):
    ev = [v for v in range(n) if len(adj[v]) % 2 == 0]
    g = ev[0] if ev else None
    Ng = adj[g] if g is not None else set()
    odd = [v for v in range(n) if len(adj[v]) % 2 == 1]
    if form == 'star':
        c = rng.choice(odd)
        A = {a for a in range(n) if a != c and a not in adj[c] and a not in Ng}
        return {'ef': {c: A}}, (c,)
    if form == 'lnmatch':
        k = rng.randint(1, K)
        free = odd[:]
        rng.shuffle(free)
        ef = {}
        used = set()
        for c in free:
            if len(ef) >= k or c in used:
                continue
            cand = [a for a in range(n) if a not in used and a != c and a not in adj[c] and a not in Ng]
            if not cand:
                continue
            a = rng.choice(cand)
            ef[c] = {a}
            used |= {c, a}
        return {'ef': ef}, tuple(sorted(ef))
    k = rng.randint(1, min(K, len(odd)))
    C = rng.sample(odd, k)
    if form == 'bipx':
        ef = {c: set() for c in C}
        for h in range(n):
            if h in C or h in Ng:
                continue
            cand = [c for c in C if h not in adj[c]]
            if cand:
                ef[rng.choice(cand)].add(h)
        return {'ef': ef}, tuple(C)
    NC = set(C)
    for c in C:
        NC |= adj[c]
    H = [h for h in range(n) if h not in NC and h not in Ng]
    ef = {c: set() for c in C}
    if form == 'bip1u':
        D = {c: bfs(n, adj, c) for c in C}
        for h in H:
            m = min(D[c][h] for c in C)
            ef[rng.choice([c for c in C if D[c][h] == m])].add(h)
    else:
        for h in H:
            ef[rng.choice(C)].add(h)
    sysd = {'ef': ef}
    if form == 'bip1ne':
        sysd['ep'] = [(C[i], C[j]) for i in range(k) for j in range(i + 1, k)]
    return sysd, tuple(C)


def main():
    form = sys.argv[1]
    n = int(sys.argv[2])
    T = int(sys.argv[3])
    rng = random.Random(int(sys.argv[4]))
    budget = int(sys.argv[5]) if len(sys.argv) > 5 else 2000000
    K = int(sys.argv[6]) if len(sys.argv) > 6 else 4
    items = []
    for _ in range(T):
        adj = rand_graph(n, rng)
        while form == 'bipx' and any(len(adj[v]) == 2 for v in range(n) if len(adj[v]) % 2 == 0):
            adj = rand_graph(n, rng)
        sysd, C = build(form, n, adj, rng, K)
        items.append((n, adj, sysd))
    ok = fail = und = lsok = 0
    CH = 200
    for s in range(0, len(items), CH):
        chunk = items[s:s + CH]
        for (nn, adj, sysd), (st, P) in zip(chunk, solve_many(chunk, budget=budget)):
            if st == 'OK':
                assert check(nn, adj, P, sysd), 'witness check failed'
                ok += 1
            elif st == 'NONE':
                fail += 1
                print('FAIL', to_g6(nn, adj), {v: sorted(S) for v, S in sysd['ef'].items()}, sysd.get('ep', []))
                sys.stdout.flush()
            else:
                from lsls import search          # positive answers only
                Pl = search(nn, adj, sysd, steps=2000, k=3, seed=1)
                if Pl is not None:
                    ok += 1
                    lsok += 1
                else:
                    und += 1
    print(f'SUMMARY form={form} n={n} trials={T} ok={ok} (local search {lsok}) fail={fail} undecided={und}')


if __name__ == '__main__':
    main()
