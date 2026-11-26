"""Random sample of the prescribed-end lemma at odd order N (default 9).

Random connected graphs of order N with Delta(EV) <= 3; for each even y compare the odd-order
Fan game (odd_fan_game.solve, held sets <= kmax) with the exact answer (tools/pathnum2.py:
a partition into (N-1)/2 paths with an end at y).
Usage: python3 sample_prescribed.py N graphs [kmax=3] [seed=1]
"""
import os
import random
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'tools'))
import networkx as nx
from pathnum import verify_partition
from pathnum2 import decompose
from odd_fan_game import solve, ev


def main():
    N, M = int(sys.argv[1]), int(sys.argv[2])
    kmax = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    rng = random.Random(int(sys.argv[4]) if len(sys.argv) > 4 else 1)
    stats = {}
    done = 0
    while done < M:
        G = nx.gnp_random_graph(N, rng.uniform(0.25, 0.6), seed=rng.randrange(10**9))
        if not nx.is_connected(G):
            continue
        E = ev(G)
        if not E or max(dict(G.subgraph(E).degree()).values()) > 3:
            continue
        done += 1
        for y in E:
            st, P = decompose(G, (N - 1) // 2, min_ends={y: 1}, time_limit=60, workers=2)
            exact = P is not None and verify_partition(G, P)
            game = solve(G, y, kmax) is not None
            assert not (game and not exact), 'unsound game'
            key = (len(E), exact, game)
            stats[key] = stats.get(key, 0) + 1
            if not exact:
                print('NOFLOOR', nx.to_graph6_bytes(G, header=False).strip().decode(), 'y', y,
                      'e', len(E), flush=True)
    for (e, ex, g), c in sorted(stats.items()):
        print(f'e={e} exact={ex} game={g}: {c}', flush=True)


if __name__ == '__main__':
    main()
