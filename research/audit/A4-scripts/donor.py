# Reproduce the finite comparison in the proof of Theorem 11 (odd-semi-clique-boundary, Sec. 8)
import math, sys
def ceil_div(a, b): return -((-a) // b)
def pos(a): return max(a, 0)
def run(kmax, kmin=1):
    triples = 0; worst = None; fails = []
    for k in range(kmin, kmax):
        for g in range(1, k):
            if g == 1: l, D = 3, 2
            else: l, D = g, g * (g + 1) // 2
            if l + D > k: continue
            rmax = (3 * k - l + 2 * g + 2 - 3 * D) // 2
            for r in range(k + 2, rmax + 1):
                triples += 1
                u = r - k; d = ceil_div(r, 2); v = k - d
                M = r - 2 + (1 if r % 2 == 0 else 0); E = k + g - d
                rhs3 = ceil_div(2 * r + l - 5 * g - 2 + 3 * D, 3)
                okA = rhs3 >= d
                okB = M - E >= 2 * u - 1
                best = None
                for z in range(0, d + 1):
                    fub = min(d - z, 2 * v - 1 - d + z)
                    if fub < 0: continue
                    cost = z * pos(M - 3 * u + 1) + (d - z - fub) * pos(M - 4 * u + 2)
                    best = cost if best is None else min(best, cost)
                okC = (best is None) or best > E
                margin = None if best is None else best - E
                if not (okA and okB and okC):
                    fails.append((k, g, r, okA, okB, okC, best, E))
                if margin is not None and (worst is None or margin < worst[0]):
                    worst = (margin, k, g, r)
    return triples, worst, fails
if __name__ == "__main__":
    t, w, f = run(130)
    print("k<130: triples", t, "least margin", w, "fails", len(f), f[:5])
    t2, w2, f2 = run(int(sys.argv[1]) if len(sys.argv) > 1 else 600, 130)
    print("130<=k<N: triples", t2, "least margin", w2, "fails", len(f2), f2[:5])
