"""t6probe.py: how robust is the t6 base?  (session claude/clt)

For B = J - z (graph6 on stdin, U = N(z) = {0..5}) and random labellings
(x1,y1,x2,y2,x3,y3) of U with x1y2, x2y3 in E(B), build the base graph
    M = (B - x1y2 - x2y3) + z y1        (z a leaf at y1; x3 the only even vertex)
and decide the append base (t6-dense Def. 2.1 with (E7)) and variants with one condition dropped:
    E1a  P_z avoids x1          E1b  P_z ends neither at y2 nor y3
    E2   P_y2 avoids x2          E3   P_y3 avoids x3          E4  P_y2 != P_y3
    E5   P_x2 avoids y3          E7   P_x1 avoids y2
usage: t6probe.py LABS BUDGET SEED [VARIANTS] < B.g6
VARIANTS: comma list from full,-E1a,-E1b,-E2,-E3,-E4,-E5,-E7 (default full)
Prints per graph: counts of labellings with a base for each variant.
"""
import sys
import random
import itertools
from clt_lib import parse_g6, solve_many, check

RETRIES = 4
COND = ['E1a', 'E1b', 'E2', 'E3', 'E4', 'E5', 'E7']


def system(L, z, drop=()):
    x1, y1, x2, y2, x3, y3 = L
    ef, ep = {}, []
    def av(v, a):
        ef.setdefault(v, set()).add(a)
    if 'E1a' not in drop:
        av(z, x1)
    if 'E1b' not in drop:
        ep += [(z, y2), (z, y3)]
    if 'E2' not in drop:
        av(y2, x2)
    if 'E3' not in drop:
        av(y3, x3)
    if 'E4' not in drop:
        ep.append((y2, y3))
    if 'E5' not in drop:
        av(x2, y3)
    if 'E7' not in drop:
        av(x1, y2)
    return {'ef': ef, 'ep': ep}


def base_graph(nB, adjB, L):
    x1, y1, x2, y2, x3, y3 = L
    n = nB + 1
    adj = [set(a) for a in adjB] + [set()]
    for a, b in ((x1, y2), (x2, y3)):
        adj[a].discard(b)
        adj[b].discard(a)
    z = nB
    adj[z].add(y1)
    adj[y1].add(z)
    ev = [v for v in range(n) if len(adj[v]) % 2 == 0]
    assert ev == [x3], ev
    return n, adj, z


def main():
    labs = int(sys.argv[1])
    budget = int(sys.argv[2])
    rng = random.Random(int(sys.argv[3]))
    variants = sys.argv[4].split(',') if len(sys.argv) > 4 else ['full']
    for line in sys.stdin:
        g6 = line.strip()
        if not g6:
            continue
        nB, adjB = parse_g6(g6)
        allL = [p for p in itertools.permutations(range(6)) if p[3] in adjB[p[0]] and p[5] in adjB[p[2]]]
        rng.shuffle(allL)
        Ls = allL[:labs]
        counts = {}
        for var in variants:
            drop = () if var == 'full' else (var[1:],)
            items = []
            for L in Ls:
                n, adj, z = base_graph(nB, adjB, L)
                items.append((n, adj, system(L, z, drop)))
            res = solve_many(items, budget=budget)
            for seed in range(1, RETRIES + 1):      # retry undecided ones with shuffled orders
                idx = [i for i, (st, _) in enumerate(res) if st == 'UND']
                if not idx:
                    break
                res2 = solve_many([items[i] for i in idx], budget=budget, seed=seed)
                for i, r in zip(idx, res2):
                    res[i] = r
            ok = sum(1 for st, _ in res if st == 'OK')
            und = sum(1 for st, _ in res if st == 'UND')
            for it, (st, P) in zip(items, res):
                if st == 'OK':
                    assert check(it[0], it[1], P, it[2])
            counts[var] = (ok, und, len(Ls))
        print(g6, ' '.join(f'{v}:{c[0]}/{c[2]}(und {c[1]})' for v, c in counts.items()), flush=True)


if __name__ == '__main__':
    main()
