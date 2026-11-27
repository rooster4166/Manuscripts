"""A16: stress test of Lemma 3 (Fan's lemma with vertex sets) by running its proof.

For random graphs K, random path partitions D (arbitrary profiles) and every pair (t, u) with
t != u, tu not in E(K) and b(t) > |Z(u)|, run the chain construction and the execution of the
manuscript's proof (a16_core.fan) and assert every claim: a chain exists; pi(x_i, current form)
is still x_{i+1} when a path is re-used (Q_i = Q_j); no path is used three times; Q* is untouched
until the append; the result partitions K + tu; |D+| = |D|; b+ = b - 1_t + 1_u; vertex sets are
preserved except one, which gains exactly u.

Usage: python3 a16_fan_test.py [trials] [seed] [long]
  long: use long random chains (any chain of distinct vertices is allowed) instead of shortest
"""
import random
import sys

import a16_core as C

LONG = False


def main():
    trials = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    rng = random.Random(seed)
    global LONG
    LONG = len(sys.argv) > 3 and sys.argv[3] == "long"
    inst = 0
    skipped = 0
    for _ in range(trials):
        n = rng.randint(4, 13)
        p = rng.uniform(0.15, 0.7)
        K = C.random_graph(n, p, rng)
        if not C.edges(K):
            continue
        D = C.random_partition(K, rng, stop=rng.choice([0.05, 0.2, 0.5]))
        C.check_partition(K, D)
        b = C.ends_count(D, K)
        for t in K:
            for u in K:
                if t == u or u in K[t]:
                    continue
                if b[t] > len(C.Zset(K, D, u)):
                    C.fan(K, D, t, u, rng=rng, long_chain=LONG)
                    inst += 1
                else:
                    skipped += 1
    st = C.FAN_STATS
    print(f"Lemma 3: {inst} transfers executed and checked, 0 failures "
          f"({skipped} pairs (t,u) did not satisfy b(t) > |Z(u)|)")
    print("chain length histogram:", dict(sorted(st.chain_len.items())))
    print("chains re-using a path (Q_i = Q_j, j < i):", st.reuse)


if __name__ == "__main__":
    main()
