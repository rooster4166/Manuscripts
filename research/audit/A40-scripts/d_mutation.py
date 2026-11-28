"""d_mutation.py -- (d) is the routeR fix needed?  Re-run Criterion R with the two guards removed:
P may end at the head a_j (so a_j is a token of K and (TI) fails), and suppression (S) may act on a
head (the literal (S) of multi-token Def. 2.2, which excludes heads only through (TI)).  Only paths
P ending at a_j are tried.  Each schedule found is executed with the audit's own executor
(c_data.execute); a failure shows that a schedule in the sense of Def. 2.2, without (TI), does not
certify the hypothesis of Lemma R(b).
usage: python3 d_mutation.py INSTANCES COUNT SEED [noheadS]   (INSTANCES: lines 'g6 c1 a1 c2 a2')
With 'noheadS' heads are never suppressed (only the guard 'P does not end at a_j' is removed)."""
import sys, os, random
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from a40lib import dec
from c_data import execute, ek, adjof


def search(N, E, tails, heads_suppressible=True):
    seen = set()
    def rec(E, tails):
        key = (E, tails)
        if key in seen:
            return None
        seen.add(key)
        A = adjof(N, E); d = [len(a) for a in A]
        tok = [v for v in range(N) if d[v] > 0 and d[v] % 2 == 0]
        if len(tok) <= 1 and len(tails) <= 1:
            return []
        ts = set(tok); X = set()
        for (c, s, x) in tails:
            X |= {c, x}
        leaves = {c for (c, s, x) in tails}
        # try suppressions first, so that a suppression of the head is found if there is one
        for p in tok:
            if d[p] != 2 or (p in X and not heads_suppressible) or p in leaves:
                continue
            a, b = sorted(A[p])
            if b in A[a] or a in leaves or b in leaves:
                continue
            if any({a, b} == {x, s} for (c, s, x) in tails):
                continue
            r = rec(frozenset((E - {ek(p, a), ek(p, b)}) | {ek(a, b)}), tails)
            if r is not None:
                return [('S', p, a, b)] + r
        for p in tok:
            for u in sorted(A[p]):
                if d[u] % 2 == 0 or u in X:
                    continue
                if any(w in ts and w != p for w in A[u] if w != p):
                    continue
                r = rec(E - {ek(p, u)}, tails)
                if r is not None:
                    return [('M', p, u)] + r
        for i, (c, s, x) in enumerate(tails):
            if d[s] % 2 == 1:
                r = rec(E - {ek(c, s)}, tails[:i] + tails[i + 1:])
                if r is not None:
                    return [('D', c, s)] + r
        return None
    return rec(frozenset(E), tuple(tails))


def paths_to(n, F, ci, ai, target, maxlen=4):
    out = []
    def ext(P, S):
        if P[-1] == target and len(P) >= 2:
            out.append(list(P)); return
        if len(P) > maxlen:
            return
        for y in sorted(F[P[-1]]):
            if y not in S and y != ai:
                S.add(y); P.append(y); ext(P, S); P.pop(); S.discard(y)
    ext([ci], {ci})
    return out


if __name__ == '__main__':
    lines = [l.split() for l in open(sys.argv[1]) if l.strip()]
    count, seed = int(sys.argv[2]), int(sys.argv[3])
    hs = not (len(sys.argv) > 4 and sys.argv[4] == 'noheadS')
    rng = random.Random(seed)
    stat = {'instances': 0, 'schedules (P ends at a_j)': 0, 'using S at the head': 0,
            'executed OK': 0, 'EXECFAIL': 0}
    shown = 0
    for t in rng.sample(lines, min(count, len(lines))):
        g = t[0]; c1, a1, c2, a2 = map(int, t[1:5]); n, F = dec(g)
        stat['instances'] += 1
        EF = {ek(u, v) for u in range(n) for v in F[u]}
        for (ci, ai, cj, aj) in ((c1, a1, c2, a2), (c2, a2, c1, a1)):
            for P in paths_to(n, F, ci, ai, aj):
                if cj in P:
                    continue
                E = EF - {ek(x, y) for x, y in zip(P, P[1:])}
                E = E | {(cj, n)}; tails = [(n, cj, aj)]; N = n + 1
                mv = search(N, E, tails, heads_suppressible=hs)
                if mv is None:
                    continue
                stat['schedules (P ends at a_j)'] += 1
                uses = any(m[0] == 'S' and m[1] == aj for m in mv)
                stat['using S at the head'] += uses
                cert = (ci, ai, cj, aj, P, N, E, tails, mv)
                try:
                    execute(n, F, c1, a1, c2, a2, cert)
                    stat['executed OK'] += 1
                except AssertionError as e:
                    stat['EXECFAIL'] += 1
                    stat['EXECFAIL with S at the head'] = stat.get('EXECFAIL with S at the head', 0) + uses
                    if shown < 3:
                        shown += 1
                        print('EXECFAIL', g, c1, a1, c2, a2, 'i->', ci, 'P=', P, 'moves', mv, repr(e)[:160])
                break
    print(stat)
