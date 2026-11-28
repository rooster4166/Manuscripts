"""h_allodd.py (audit A37): Conjecture 7.2 check with my own exhaustive Lovasz enumeration.
Every connected graph of order n with all degrees odd (nauty-geng -c, filtered here); every choice
of distinct c, x, a, b with cx, ab non-edges ((c,x) ordered, {a,b} unordered); is there a Lovasz
decomposition with x not in Q(c) and (a not in Q(b) or b not in Q(a))?  Per choice the enumeration
stops at the first good decomposition (cap CAP decompositions; 'undecided' if reached).
usage: python3 h_allodd.py n CAP
"""
import itertools
import subprocess
import sys
from collections import Counter

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from a37lib import adjacency, connected_without, g6_decode
from h_bases8 import ends_path, lovasz_gen


def main():
    n0, cap = int(sys.argv[1]), int(sys.argv[2])
    out = subprocess.run(["nauty-geng", "-q", "-c", str(n0)], capture_output=True, text=True).stdout.split()
    st = Counter()
    for g6 in out:
        n, E = g6_decode(g6)
        A = adjacency(n, E)
        if any(len(A[v]) % 2 == 0 for v in range(n)) or not connected_without(n, A, set()):
            continue
        st["graphs"] += 1
        cache = []
        gen = lovasz_gen(n, E, [1] * n)
        exhausted = False
        for c, x in itertools.permutations(range(n), 2):
            if x in A[c]:
                continue
            for a, b in itertools.combinations([v for v in range(n) if v not in (c, x)], 2):
                if b in A[a]:
                    continue
                st["choices"] += 1

                def good(Q):
                    return x not in Q[c] and (a not in Q[b] or b not in Q[a])
                ok = any(good(Q) for Q in cache)
                while not ok and not exhausted and len(cache) < cap:
                    try:
                        D = next(gen)
                    except StopIteration:
                        exhausted = True
                        break
                    Q = ends_path(D)
                    cache.append(Q)
                    ok = good(Q)
                if ok:
                    st["ok"] += 1
                elif exhausted:
                    st["FAIL"] += 1
                    print("FAIL", g6, c, x, a, b, flush=True)
                else:
                    st["undecided (cap)"] += 1
    print(n0, dict(st))


if __name__ == "__main__":
    main()
