#!/usr/bin/env python3
"""A19 audit of near-dirac: numerical checks of the constants in
Prop 8.3(ii) and of the parameter choices in the proof of Theorem 9.3.

All quantities of Theorem 9.3 are evaluated at their worst-case bounds from
the proof, as functions of xi (the error rate) and n, with the paper's
example choice q = xi^(1/5) n, omega = xi^(-1/100).  Logarithms (base 10) are
used so that tiny xi does not underflow.

Output: out/params.txt (also printed).
"""
import math

OUT = []


def log(*a):
    s = " ".join(str(x) for x in a)
    OUT.append(s)
    print(s)


# ---------------------------------------------------------------------------
# 1. Prop 8.3(ii): s^2/2 + s(2s+1) <= 3s^2 + 3 <= D/8 when s <= sqrt(D)/6 ?
# ---------------------------------------------------------------------------
def prop83ii():
    log("== Prop 8.3(ii): error bound vs tolerance D/8 ==")
    bad_chain, bad_true = [], []
    for D in range(2, 20001, 2):
        smax = int(math.isqrt(D) // 6)
        # exact floor of sqrt(D)/6
        while (smax + 1) * 6 <= math.sqrt(D):
            smax += 1
        while smax > 0 and smax * 6 > math.sqrt(D):
            smax -= 1
        for s in range(0, smax + 1):
            true_err = s * (s - 1) / 2 + s * (2 * s + 1)     # binom(s,2) + s(2s+1)
            paper_err = s * s / 2 + s * (2 * s + 1)
            if 3 * s * s + 3 > D / 8:
                bad_chain.append((s, D))
            if paper_err > D / 8:
                bad_true.append((s, D))
    log(f"  pairs (s, D) with s <= sqrt(D)/6, D <= 20000 even, where 3s^2+3 > D/8 (the printed chain fails): "
        f"{len(bad_chain)}; first few {bad_chain[:6]}")
    log(f"  pairs where s^2/2 + s(2s+1) > D/8 (the needed bound fails): {len(bad_true)}")
    log("  => the conclusion holds for every D; only the intermediate '<= 3s^2+3 <= D/8' needs D >= 72"
        " (or the case s = 0 treated separately).")


# ---------------------------------------------------------------------------
# 2. Theorem 9.3 parameters
# ---------------------------------------------------------------------------
def thm93():
    log("\n== Theorem 9.3: q = xi^(1/5) n, omega = xi^(-1/100) ==")
    # (a) the displayed requirement q >= omega (xi^(1/3) + xi^(1/4)) n
    #     <=> xi^(1/5) >= xi^(1/3 - 1/100) + xi^(1/4 - 1/100)
    lo, hi = -400.0, 0.0     # log10 xi
    f = lambda L: 10 ** (L / 5) - 10 ** (L * (1 / 3 - 0.01)) - 10 ** (L * (1 / 4 - 0.01))
    # find the largest log10 xi where f >= 0
    for _ in range(200):
        mid = (lo + hi) / 2
        if f(mid) >= 0:
            lo = mid
        else:
            hi = mid
    log(f"  displayed requirement holds iff xi <= 10^{lo:.2f} (about {10**lo:.2e}); fine since xi_n -> 0")

    log("  worst-case ratios (each must tend to 0); 'n-term' is the extra n/q^2 from the '+1' in |W|:")
    log(f"  {'log10 xi':>9} | {'|X|/q':>9} {'lambda/q':>9} {'h/q':>9} {'n h/q^2':>9} {'n|W|/q^2':>9} | "
        f"{'Prop8.3 hyp':>11} {'d<=5D/4':>8} {'lam/(xi n)':>10}")
    for L in (-2, -5, -10, -30, -100, -200, -300):
        xi = 10.0 ** L
        X_q = 4 * xi ** 0.6                      # |X| <= 4 xi n^2/q
        lam_q = xi ** (0.2 + 0.01)               # lambda/q = q/(n omega)
        h_q = 2 * lam_q + 3 * xi ** 0.8 + X_q    # h <= 2 lambda + 3 xi n + |X|
        nh_q2 = 2 * xi ** 0.01 + 3 * xi ** 0.6 + 4 * xi ** 0.4
        nW_q2 = xi ** 0.6 + 8 * xi ** 0.4        # + n/q^2 (separately)
        hyp = 2 * xi ** 0.8 + 16 * xi ** 0.6     # (xi n + 3|X| + |Delta_H|)/q, |Delta_H| <= xi n + |X|
        deg = xi + 1.25 * xi ** 0.2 <= 1 / 8     # n/2 + xi n <= 5(n/2 - q)/4
        lam_xin = 10 ** ((0.41 - 1) * L)         # lambda / (xi n) = xi^(0.41-1)
        log(f"  {L:>9} | {X_q:9.2e} {lam_q:9.2e} {h_q:9.2e} {nh_q2:9.2e} {nW_q2:9.2e} | "
            f"{hyp:11.2e} {str(deg):>8} {lam_xin:10.2e}")
    log("  note: n h/q^2 contains 2/omega = 2 xi^(1/100): it tends to 0, but only at xi ~ 10^-100 is it 0.2.")

    log("\n  The '+1' in |W| <= |Delta_H| + |X| + 1 gives n|W| >= n whenever |W| >= 1.  n/q^2 = 1/(n xi^(2/5)):")
    for (n, L) in ((10 ** 6, -2), (10 ** 6, -10), (10 ** 6, -15), (10 ** 9, -20), (10 ** 9, -25)):
        xi = 10.0 ** L
        q = xi ** 0.2 * n
        log(f"    n = 10^{round(math.log10(n))}, xi = 1e{L}: q = {q:.3g}, n/q^2 = {n / q**2:.3g}")
    log("    With xi_n = n^-3 (allowed: xi_n is only an upper bound tending to 0): q = n^(2/5), n/q^2 = n^(1/5) -> oo.")
    log("    In that case X is empty, |Delta_H| <= 1, and Lemma 8.2 with s = 0 returns t = 0, |W| = |Delta_H|,")
    log("    so |W| = 1 at odd n and (H1) n|W| = o(q^2) FAILS.  Fix: replace xi_n by max(xi_n, 1/log n).")

    log("\n  Is regime (b) non-vacuous?  |X| <= 4 xi^(4/5) n  versus  sqrt(D)/6 ~ sqrt(n/2)/6:")
    for (n, L) in ((10 ** 8, -2), (10 ** 12, -3), (10 ** 20, -5)):
        xi = 10.0 ** L
        log(f"    n=1e{round(math.log10(n))}, xi=1e{L}: max |X| bound {4 * xi ** 0.8 * n:.3g}, sqrt(D)/6 {math.sqrt(n / 2) / 6:.3g}")


def main():
    prop83ii()
    thm93()
    with open(__file__.rsplit('/', 1)[0] + '/out/params.txt', 'w') as f:
        f.write("\n".join(OUT) + "\n")


if __name__ == '__main__':
    main()
