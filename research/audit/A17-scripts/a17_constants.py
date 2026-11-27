#!/usr/bin/env python3
"""A17: every numerical inequality in the proof of Theorem 1.1 and Corollary 1.2
of manuscripts/near-dirac/near-dirac.tex, evaluated with the paper's constants.

Constants (paper, section 4 'Constants'):
    theta = min(eps/2, 1/100),  c = theta/1000,
    q = least integer >= theta*m with q == m (mod 2),  D = m - q.
For each eps we scan m upward and report the least m from which every inequality
holds (checked on a long window, and at worst cases of the free parameters).
Worst cases are taken over: degrees in [m - cm, m + 1 + cm], |X| <= cm,
b in {0,1,2}, |b(A)-b(B)| <= cm, rho in {0,1}.

Also: a grid check of f(x,y) < 0 (Lemma 3.1) independent of Lean, and the
maximum of f on [0,0.65]^2.
"""
import math
from fractions import Fraction as Fr


def consts(eps, m):
    theta = min(eps / 2, 1 / 100)
    c = theta / 1000
    q = math.ceil(theta * m)
    if (q - m) % 2:
        q += 1
    D = m - q
    return theta, c, q, D


def checks(eps, m):
    """Return dict name -> bool for every inequality used, at worst cases."""
    th, c, q, D = consts(eps, m)
    cm = c * m
    X = math.floor(cm)  # |X| <= cm
    out = {}
    out['D even'] = (D % 2 == 0)
    out['theta m <= q <= theta m + 2'] = th * m <= q <= th * m + 2
    out['cm <= q/1000'] = cm <= q / 1000 + 1e-12
    out['q <= m/100 + 2'] = q <= m / 100 + 2
    # Step 0: p_v in [0.49q, 0.51q]; degrees in [m-cm, m+1+cm]
    pmin = (m - cm + 0 - D) / 2
    pmax = (m + 1 + cm + 2 - D) / 2
    out['S0 p_v >= 0.49q'] = pmin >= 0.49 * q
    out['S0 p_v <= 0.51q'] = pmax <= 0.51 * q
    # Step 1: Lambda_0 - e_H(B) <= 1.5cm <= 0.6q ; Lambda_0 + e_H(A) >= -q/2 - 1.5cm >= -0.6q
    out['S1 upper'] = 1.5 * cm <= 0.6 * q
    out['S1 lower'] = -q / 2 - 1.5 * cm >= -0.6 * q
    # Step 2: available end vertices with b>=1 in H_A: >= (m - cm/2 - 2|X|)/2 >= 1.6q
    avail = (m - cm / 2 - 2 * X) / 2
    out['S2 avail >= 0.45m'] = avail >= 0.45 * m
    out['S2 0.45m >= 2q'] = 0.45 * m >= 2 * q
    # Step 3: |F| <= (2m+1)cm/2 <= 1.01 c m^2 ; full slots <= |F|/floor(m/100); 2cm+2 more
    cap3 = math.floor(m / 100)
    F = (2 * m + 1) * cm / 2
    out['S3 |F| <= 1.01cm^2'] = F <= 1.01 * c * m * m
    full = F / cap3 if cap3 >= 1 else float('inf')
    out['S3 full+2cm+2 < q'] = full + 2 * cm + 2 < q
    out['S3 full <= 101cm (paper)'] = full <= 101 * cm + 1e-9
    # Step 4: partners. cap q/100 (integer part); vertices at cap <= 2*sum p_x / cap
    cap4 = math.floor(q / 100)
    if cap4 < 1:
        out['S4 cap q/100 >= 1'] = False
    else:
        out['S4 cap q/100 >= 1'] = True
    p_x_max = pmax
    capped = (2 * p_x_max * X) / cap4 if cap4 >= 1 else float('inf')
    excl = 2 * p_x_max + (2 + 2 * cap3 + 2 * X) + capped
    out['S4 healthy cross nbrs - excluded >= 2'] = (m / 4 - cm) - excl >= 2
    out['S4 excluded <= 0.032m + 2 (paper)'] = excl <= 0.032 * m + 2
    # Step 5: row forced <= 1 + cm + q/100 <= 0.02q ; column forced <= 2 + 2 cap3 + 2X <= 0.021 m <= 0.03(m - cm)
    out['S5 row forced <= 0.02q'] = 1 + cm + q / 100 <= 0.02 * q
    colf = 2 + 2 * cap3 + 2 * X
    out['S5 col forced <= 0.021m'] = colf <= 0.021 * m
    out['S5 0.021m <= 0.03|H_A|'] = 0.021 * m <= 0.03 * (m - X)
    # Step 6: h^A in [0.49|H_A|-1, 0.51|H_A|+1], h^B in [0.47|H_B|, 0.53|H_B|]
    HA_lo, HA_hi = m - X, m
    HB_lo, HB_hi = m - X, m + 1
    hA_lo = 0.49 * HA_lo - 1
    hA_hi = 0.51 * HA_hi + 1
    diff = cap3 + X + 1
    out['S6 h^B >= 0.47|H_B|'] = hA_lo - diff >= 0.47 * HB_hi
    out['S6 h^B <= 0.53|H_B|'] = hA_hi + diff <= 0.53 * HB_lo
    # matrix margins
    out['S6 rows in [0.4q,0.6q]'] = (0.49 * q - 0.02 * q >= 0.4 * q) and (0.51 * q <= 0.6 * q)
    out['S6 A cols >= 0.4|H_A|'] = hA_lo - colf >= 0.4 * HA_hi
    out['S6 A cols <= 0.6|H_A|'] = hA_hi <= 0.6 * HA_lo
    out['S6 B cols >= 0.4|H_B|'] = 0.47 * HB_lo - colf >= 0.4 * HB_hi
    out['S6 B cols <= 0.6|H_B|'] = 0.53 * HB_hi <= 0.6 * HB_lo
    # Step 8: M = cm + 1.02q <= 1.03q ; min blocks >= 0.45m >= 4M+2
    M = cm + 2 * pmax
    out['S8 M <= 1.03q'] = M <= 1.03 * q
    minblk = min(hA_lo - cap3 - X, 0.47 * HB_lo - cap3 - X)
    out['S8 min blocks >= 0.45m'] = minblk >= 0.45 * m
    out['S8 min blocks >= 4M+2'] = minblk >= 4 * M + 2
    # Step 9: e_R(S) <= 1.01cm^2 + 0.76cm^2 <= eps N^2 - D, N = 2m+2 (worst, rho=0)
    eR = 1.01 * c * m * m + X * (1 + c - 0.25) * m
    out['S9 I_X <= 0.76cm^2'] = X * (1 + c - 0.25) * m <= 0.76 * c * m * m
    out['S9 e_R + D <= eps N^2'] = eR + D <= eps * (2 * m + 2) ** 2
    out['S9 D >= (1/2-eps)(2m+3)'] = D >= (0.5 - eps) * (2 * m + 3)
    out['L4.2 D/2 >= 2'] = D >= 4
    return out


def cor12_checks(eps, m, rho):
    th, c, q, D = consts(eps, m)
    cm = c * m
    gamma = c * c / 20
    n = 2 * m + rho
    out = {}
    Xb = 4 * gamma * n * n / (cm)
    out['C1.2 |X| <= 17 gamma m / c'] = Xb <= 17 * gamma * m / c
    out['C1.2 |X| <= cm'] = Xb <= cm
    out['C1.2 mis <= cm'] = 1 + gamma * n + cm / 2 <= cm
    out['C1.2 d(x) >= (1-c)m'] = (0.5 - gamma) * n >= (1 - c) * m
    out['C1.2 d(x) <= (1+c)m'] = (0.5 + gamma) * n <= (1 + c) * m
    out['C1.2 n/8 >= m/4'] = n / 8 >= m / 4
    out['C1.2 gamma n/2 <= cm'] = gamma * n / 2 <= cm
    out['C1.2 2 <= cm'] = 2 <= cm
    return out


def least_m(eps, fn, extra=()):
    """least m0 such that all checks hold on m in [m0, 1.3*m0] (sampled densely) ."""
    lo = 10
    # exponential search
    m = lo
    while True:
        res = fn(eps, m, *extra)
        if all(res.values()):
            # verify a window
            ok = True
            for mm in range(m, int(m * 1.3) + 50, max(1, m // 2000)):
                if not all(fn(eps, mm, *extra).values()):
                    ok = False
                    break
            if ok:
                break
        m = int(m * 1.05) + 1
        if m > 10 ** 13:
            return None, res
    # bisect down
    a, b = lo, m
    while b - a > max(1, a // 10000):
        mid = (a + b) // 2
        if all(fn(eps, mid, *extra).values()):
            b = mid
        else:
            a = mid
    return b, fn(eps, b, *extra)


def matrix_f_grid(N=1300):
    best = -1e9
    arg = None
    for i in range(N + 1):
        x = 0.65 * i / N
        for j in range(N + 1):
            y = 0.65 * j / N
            f = 0.6 * x + 0.6 * y - 0.4 - x * y + 0.03 * min(x, y)
            if f > best:
                best, arg = f, (x, y)
    return best, arg


def matrix_f_exact_max():
    # On y<=x: g = 0.6x + 0.63y - 0.4 - xy; boundary maxima (exact rationals)
    cands = []
    # y = 0
    cands.append((Fr(13, 20), Fr(0), Fr(3, 5) * Fr(13, 20) - Fr(2, 5)))
    # x = 0.65
    for y in (Fr(0), Fr(13, 20)):
        x = Fr(13, 20)
        cands.append((x, y, Fr(3, 5) * x + Fr(63, 100) * y - Fr(2, 5) - x * y))
    # y = x: 1.23x - 0.4 - x^2, max at 0.615
    x = Fr(123, 200)
    cands.append((x, x, Fr(123, 100) * x - Fr(2, 5) - x * x))
    return max(cands, key=lambda t: t[2])


if __name__ == '__main__':
    print('Lemma 3.1: f = 0.6x+0.6y-0.4-xy+0.03min(x,y) on [0,0.65]^2')
    b, a = matrix_f_grid()
    print(f'  grid max {b:.6f} at {a}')
    x, y, v = matrix_f_exact_max()
    print(f'  exact boundary max {float(v):.6f} = {v} at ({x},{y})')
    print('  (critical point of g on y<=x: (0.63,0.60), a saddle; Hessian [[0,-1],[-1,0]])')
    print()
    for eps in (1e-2, 1e-3, 1e-4, 1e-6):
        m0, res = least_m(eps, checks)
        th, c, q, D = consts(eps, m0)
        print(f'eps_ex={eps:g}: theta={th:g}, c={c:g}; all Theorem 1.1 inequalities hold from m0 ~ {m0:,} (q={q})')
        # which fails last
        prev = checks(eps, max(10, int(m0 * 0.9)))
        bad = [k for k, v in prev.items() if not v]
        print(f'   binding below m0 (at 0.9*m0): {bad}')
        for rho in (0, 1):
            m1, res1 = least_m(eps, cor12_checks, (rho,))
            print(f'   Cor 1.2 (rho={rho}) inequalities hold from m ~ {m1:,}')
    print()
    # Show the paper's specific sloppy spots explicitly at a moderate m.
    eps = 1e-2
    m = 10 ** 6
    r = checks(eps, m)
    bad = [k for k, v in r.items() if not v]
    print('eps=1e-2, m=1e6: ' + (', '.join(bad) if bad else 'all inequalities hold'))
