"""Audit A22c: run construct.py (the proof of Theorem 8.2, executed) on every configuration with a
base, for instances from a g6(J - z) file (simple pairings) or from the general n <= 8 list.
usage: construct_run.py G6FILE MODE SEEDS [flag=1 ...] [start step] [maxchains=K]
  MODE walk3 | all ; SEEDS = number of random seeds per base chain."""
import sys, collections
from count_J import g6_decode, pairings
from chain import FLAGS, configs, chains, base_test
import construct


def main():
    fn, mode, seeds = sys.argv[1], sys.argv[2], int(sys.argv[3])
    fl = dict(FLAGS); nums = []; maxchains = 1
    for a in sys.argv[4:]:
        if a.startswith('maxchains='):
            maxchains = int(a.split('=')[1])
        elif '=' in a:
            k, v = a.split('='); fl[k] = bool(int(v))
        elif a.isdigit():
            nums.append(int(a))
    start, step = (nums[0], nums[1]) if len(nums) >= 2 else (0, 1)
    lines = [l.split()[0] for l in open(fn) if l.strip()]
    stat = collections.Counter(); fails = collections.Counter(); ex = {}
    for idx in range(start, len(lines), step):
        s = lines[idx]
        n, B = g6_decode(s)
        deg = [sum(r) for r in B]
        ev = [v for v in range(n) if deg[v] % 2 == 0]
        E0 = {frozenset((u, v)) for v in range(n) for u in range(v) if B[u][v]}
        for F in pairings(ev):
            if any(B[a][b] for a, b in F):
                continue
            E = E0 | {frozenset(p) for p in F}
            for X, Y in configs(F):
                k = 0
                for P2, P1 in chains(n, E, X, Y, fl, mode):
                    if k >= maxchains:
                        break
                    try:
                        D, _ = base_test(n, E, X, Y, P2, P1)
                    except AssertionError:
                        stat['parity_broken'] += 1; continue
                    if D is None:
                        continue
                    k += 1
                    stat['base_chains'] += 1
                    for sd in range(seeds):
                        try:
                            log = construct.run(n, E, X, Y, P2, P1, seed=1000 * sd + 7)
                            stat['runs_ok'] += 1
                            stat['fan_steps'] += len(log)
                        except construct.ClaimFailed as e:
                            msg = str(e).split(' = ')[0]
                            fails[msg] += 1
                            ex.setdefault(msg, (s, F, X, Y, P2, P1, sd))
    print(f'{fn.split("/")[-1]} mode={mode} flags={ {k: v for k, v in fl.items() if v} } seeds={seeds}: {dict(stat)}')
    for m, c in fails.most_common():
        print(f'  CLAIM FAILED x{c}: {m}\n     e.g. {ex[m]}')


if __name__ == '__main__':
    main()
