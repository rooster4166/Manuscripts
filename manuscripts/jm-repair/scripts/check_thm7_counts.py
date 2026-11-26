"""Check the counting inequalities in the proof of JM Theorem 7 (both cases),
for 6 <= n <= NMAX, 1 <= t <= n, n+1 <= r <= (3t-1)/2 (integers).
We check the inequality actually needed in each claim (not only JM's
lower-bounding functions f_n, f_{n,t}, g_n), donor availability after the
exclusions of the corrected transfer lemma, and retained sizes."""
import sys
NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 1500
bad = []; cnt = 0
for n in range(6, NMAX + 1):
    for t in range(1, n + 1):
        for r in range(n + 1, (3 * t - 1) // 2 + 1):
            cnt += 1
            s = (r + 1) // 2; delta = r % 2
            if not (s <= t): bad.append(("s<=t", n, t, r))
            # non-donor classes keep >= r-2-(t-s) >= 2r-2n-1
            if r - 2 - (t - s) < 2 * r - 2 * n - 1: bad.append(("nondonor", n, t, r))
            if 3 * r <= 4 * n - 1:            # Case 1
                if not (1 <= n - s <= s): bad.append(("c1 idx", n, t, r))
                # claim |P_{n-s}| >= 4r-4n-1: else t-s >= (2s-n+1)(r-2-(4r-4n-2))
                if not (t - s < (2 * s - n + 1) * (4 * n - 3 * r)): bad.append(("c1 claim", n, t, r))
                D = 4 * r - 4 * n - 1
                if D - 3 < 2 * r - 2 * n - 2: bad.append(("c1 avail1", n, t, r))
                if D - 1 < 2 * r - 2 * n: bad.append(("c1 avail2", n, t, r))
                if D - (2 * r - 2 * n) < 2 * r - 2 * n - 1: bad.append(("c1 keep", n, t, r))
            else:                              # Case 2 (r >= 4n/3)
                if not (3 * r >= 4 * n): bad.append(("gap", n, t, r))
                eps = 1 if t == n else 0
                if not (2 * n - 2 * s <= s): bad.append(("c2 idx", n, t, r))
                if not (t - s < (3 * s - 2 * n + 1) * (3 * n - 2 * r - delta + eps)): bad.append(("c2 claim", n, t, r))
                D = 3 * r - 3 * n - eps
                if r - n - 2 < 0: bad.append(("c2 neg", n, t, r))
                if D - 3 < r - n - 2: bad.append(("c2 avail1", n, t, r))
                if D - 2 * (r - n - 1) - 1 < r - n: bad.append(("c2 avail2", n, t, r))
                if t < n:
                    if D - 1 < r - n - 1: bad.append(("c2 avail3", n, t, r))
                    if D - 2 * (r - n - 1) - 1 < r - n + 1: bad.append(("c2 avail4", n, t, r))
                moved = (r - n + 1) if t < n else (r - n)
                if D - moved < 2 * r - 2 * n - 1: bad.append(("c2 keep", n, t, r))
                if n + t - 2 * s > 2 * n - 2 * s or t - s < 0: bad.append(("c2 ranges", n, t, r))
            if r > 2 * t - 1: bad.append(("r<=2t-1", n, t, r))
print("triples:", cnt, "violations:", len(bad), bad[:5])
