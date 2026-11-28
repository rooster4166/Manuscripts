"""A42: number of unlabelled graphs with all degrees odd on n vertices, by Burnside's lemma
(independent of gen.c), and the connected ones by the inverse Euler transform.
For each cycle type, take a representative permutation, compute its orbits on vertex pairs,
and count fixed graphs with all degrees odd = solutions of a GF(2) linear system."""
import itertools, math
from fractions import Fraction

def partitions(n, m=None):
    if m is None: m = n
    if n == 0: yield []; return
    for k in range(min(n, m), 0, -1):
        for p in partitions(n - k, k): yield [k] + p

def zee(lam):
    z = 1
    for k in set(lam):
        c = lam.count(k); z *= k ** c * math.factorial(c)
    return z

def rank_gf2(rows):
    rows = [r for r in rows]; r = 0
    piv_rows = []
    basis = []
    for row in rows:
        x = row
        for b in basis:
            x = min(x, x ^ b)
        if x: basis.append(x); basis.sort(reverse=True)
    return len(basis), basis

def fixed_allodd(lam):
    n = sum(lam); perm = []; s = 0
    for k in lam:
        perm += [s + (i + 1) % k for i in range(k)]; s += k
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    seen = {}; orbits = []
    for p in pairs:
        if p in seen: continue
        orb = []; q = p
        while q not in seen:
            seen[q] = len(orbits); orb.append(q)
            a, b = perm[q[0]], perm[q[1]]; q = (min(a, b), max(a, b))
        orbits.append(orb)
    no = len(orbits)
    # augmented rows: bits 0..no-1 coefficients, bit no = rhs 1
    rows = []
    for v in range(n):
        r = 0
        for k, orb in enumerate(orbits):
            c = sum(1 for (a, b) in orb if v in (a, b))
            if c % 2: r |= 1 << k
        rows.append(r | (1 << no))
    rk_aug, basis = rank_gf2(rows)
    rk, _ = rank_gf2([r & ((1 << no) - 1) for r in rows])
    if rk_aug != rk: return 0
    return 2 ** (no - rk)

def allodd(n):
    tot = Fraction(0)
    for lam in partitions(n):
        tot += Fraction(fixed_allodd(lam), zee(lam))
    assert tot.denominator == 1
    return int(tot)

A = {0: 1}
for n in range(1, 11): A[n] = allodd(n)
print('all-odd graphs (possibly disconnected):', {n: A[n] for n in range(2, 11, 2)})
# inverse Euler transform: prod_k (1-x^k)^(-C_k) = sum A_n x^n
C = {}
def euler(C, N):
    # coefficients of prod (1-x^k)^(-C_k) up to N
    a = [1] + [0] * N
    for k, ck in C.items():
        for _ in range(ck):
            for m in range(k, N + 1): a[m] += a[m - k]
    return a
for n in range(1, 11):
    C[n] = 0
    a = euler(C, n)
    C[n] = A[n] - a[n]
print('connected all-odd graphs:', {n: C[n] for n in range(2, 11, 2)})
