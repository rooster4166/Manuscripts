"""One-sided separation: K with at most one positive-even vertex, s of odd degree.  Is there a
Lovasz decomposition whose path at s stays in the ball B_2(s)?  (For s a leaf at c this is the
statement Q_c within N[c] for K - s.)  Also the leaf case directly: F all odd, c, Q_c within N[c].
Usage: python3 ball_test.py trials budget mode   (mode: z | leaf)"""
import random
import sys

import networkx as nx

import rd_lib as L
from l1_search import fix_parity_except
from lovasz_matching import make_all_odd


def main():
    trials, L.BUDGET, L.FINAL = int(sys.argv[1]), int(sys.argv[2]), False
    mode = sys.argv[3]
    rng = random.Random(31337)
    tot = bad = und = 0
    for it in range(trials):
        n = rng.randint(6, 12)
        F = nx.gnp_random_graph(n, rng.uniform(0.15, 0.6), seed=rng.randrange(10 ** 9))
        if mode == "z":
            if n % 2 == 0 or not fix_parity_except(F, rng, 0) or F.degree(0) == 0:
                continue
            b = [0 if v == 0 else 1 for v in range(n)]
            cand = [v for v in F if v != 0 and F.degree(v) % 2 == 1]
            r = 2
        else:
            if n % 2 or not make_all_odd(F, rng):
                continue
            b = [1] * n
            cand = list(F)
            r = 1
        if F.number_of_edges() > 100:
            continue
        for s in rng.sample(cand, min(3, len(cand))):
            dist = nx.single_source_shortest_path_length(F, s)
            Y = {v for v in F if dist.get(v, 99) > r}
            if not Y:
                continue
            res = L.avoid(F, b, {s: Y})
            tot += 1
            if res is None:
                und += 1
            elif not res:
                bad += 1
                if bad <= 5:
                    print("FAIL", n, sorted(F.edges()), "s", s, flush=True)
    print(mode, f"total {tot} failures {bad} undecided {und}")


if __name__ == "__main__":
    main()
