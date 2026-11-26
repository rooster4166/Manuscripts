"""Brute-force check of the terminal-step classification (Theorem 2 of d6-frontier.tex).

B-form: U = {0..5} induces K6; F = full vertices (adjacent to all of U; F-F adjacency
given).  A final partition into k paths has excess sum 6, where excess = b - 1 on odd
vertices and b on U.  For a local last edge uv (u, v in U + F) with receiver v and donor u,
Fan's single inequality needs b'(u) = b(u)+1 > #blank neighbours of v in G - uv, and the
local blanks give a lower bound for the right side.  We enumerate all excess distributions
on U + F (+ exterior excess) and list those that survive for some local edge, with the
root condition b(r) >= 2 for some r.  W-form analogue: T = {0..4} induces K5, r odd adjacent
to T, excess sum 4."""
import itertools

def survivors(U, F, adjF, budget, odd_local, root_needed):
    L = U + F
    adj = {v: set() for v in L}
    for a, b in itertools.combinations(U, 2): adj[a].add(b); adj[b].add(a)
    for f in F:
        for u in U: adj[f].add(u); adj[u].add(f)
    for a, b in adjF: adj[a].add(b); adj[b].add(a)
    out = set()
    # excess values: even on every vertex; U gets b = excess, odd local gets b = 1 + excess
    def rec(i, left, cur):
        if i == len(L):
            for ext in range(0, left + 1, 2):
                if ext == left:
                    yield dict(cur), ext
            return
        for e in range(0, left + 1, 2):
            cur[L[i]] = e
            yield from rec(i + 1, left - e, cur)
        del cur[L[i]]
    for exc, ext in rec(0, budget, {}):
        b = {v: (1 + exc[v]) if v in odd_local else exc[v] for v in L}
        if root_needed and not any(b[u] >= 2 for u in U if u not in odd_local):
            continue
        for v in L:
            if b[v] < 1: continue
            for u in adj[v]:
                bp = dict(b); bp[u] += 1; bp[v] -= 1
                blanks = sum(1 for w in adj[v] if w != u and bp[w] == 0)
                if bp[u] > blanks:
                    prof = tuple(sorted(((w, b[w]) for w in L if (b[w] != (1 if w in odd_local else 0))), key=str))
                    out.add((prof, ext, (u, v)))
    return out

def classify(p, ext, Uset, Fset):
    d = dict(p)
    if ext: return 'other'
    uvals = sorted((d[w] for w in d if w in Uset), reverse=True)
    fvals = sorted((d[w] for w in d if w in Fset), reverse=True)
    if fvals == [] and uvals == [4, 2]: return 'alpha (U-hub 4 + one double)'
    if fvals == [] and uvals == [6]: return 'beta (U-hub 6)'
    if fvals == [5] and uvals == [2]: return 'gamma (full hub 5 + one double)'
    if fvals == [] and uvals == [4]: return 'alpha_W (T-hub 4)'
    if fvals == [5] and uvals == []: return 'gamma_W (odd local hub 5)'
    return 'other'

def show(name, S, Uset, Fset):
    profs = {(p, e) for p, e, _ in S}
    types = {}
    for p, e in profs:
        types.setdefault(classify(p, e, Uset, Fset), []).append(dict(p))
    print(name, ": surviving end profiles =", len(profs))
    for t, L in sorted(types.items()):
        print("   ", t, ":", len(L), "profiles, e.g.", L[0])
    assert 'other' not in types, types.get('other')

U = list(range(6))
show("B-form, one full vertex f", survivors(U, ['f'], [], 6, {'f'}, True), set(U), {'f'})
show("B-form, two adjacent full vertices f, g", survivors(U, ['f', 'g'], [('f', 'g')], 6, {'f', 'g'}, True), set(U), {'f', 'g'})
show("B-form, two non-adjacent full vertices f, g", survivors(U, ['f', 'g'], [], 6, {'f', 'g'}, True), set(U), {'f', 'g'})
T = list(range(5))
show("W-form (T = K5, r and one full f odd, r ~ f)", survivors(T, ['r', 'f'], [('r', 'f')], 4, {'r', 'f'}, False), set(T), {'r', 'f'})
print("terminal classification confirmed: no tight standard profile survives a local last step")
