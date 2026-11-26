"""Brute-force check of the per-colour inequalities used in the proofs of the
cut conditions (UH) and (LH) (Lemmas on u_i and s_i in the manuscript).
For each K, colour type (T, c, S), p, and split p = n0+n1+n2 we compute
  fA = 2 n0 + n1, fB = n1 + 2 n2, psi = n1+n2+[n2>=1 and type != c],
  delta = (p + eps - K)^+, eps = 4 (T), 3 (c), 5 (S),
  Delta = (delta - psi)^+, s = 2 fA - K Delta,
  kappa = 4 (T,S), 2 (c), u = K min(kappa, psi) - 2 fB."""
bad = []
for K in range(4, 61):
    for typ in "TcS":
        pmax = K if typ == "T" else K - 1
        eps = {"T": 4, "c": 3, "S": 5}[typ]
        kap = 2 if typ == "c" else 4
        for p in range(1, pmax + 1):
            for n0 in range(p + 1):
                for n1 in range(p - n0 + 1):
                    n2 = p - n0 - n1
                    fA, fB = 2 * n0 + n1, n1 + 2 * n2
                    psi = n1 + n2 + (1 if (n2 >= 1 and typ != "c") else 0)
                    delta = max(0, p + eps - K)
                    D = max(0, delta - psi)
                    s = 2 * fA - K * D
                    u = K * min(kap, psi) - 2 * fB
                    tag = (K, typ, p, n0, n1, n2)
                    # ---- (LH) lemmas
                    if typ == "T":
                        if s < 0: bad.append(("T s<0", tag))
                        if D % 2 == 1 and s < K - 4: bad.append(("T odd", tag))
                    if typ == "c":
                        if s < 0: bad.append(("c s<0", tag))
                        if D % 2 == 1 and s < 3 * K - 8: bad.append(("c odd", tag))
                    if typ == "S":
                        if s < -4: bad.append(("S s<-4", tag))
                        J = (n0 == K - 1)
                        if J and not (D == 4 and s == -4): bad.append(("S J", tag))
                        if not J and K >= 8 and s < 0: bad.append(("S nonJ s<0", tag))
                        if not J and D % 2 == 1:
                            special = (n0 == K - 2 and n1 == 0)
                            if special and s != K - 8: bad.append(("S special", tag))
                            if not special and s < K - 6: bad.append(("S odd", tag))
                    # ---- (UH) lemmas
                    if typ != "c":
                        if u < 0: bad.append(("u<0", tag))
                        if fB > 0 and psi <= 4 and u < K - 2: bad.append(("u small", tag))
                        if psi >= 5 and u != 4 * K - 2 * fB: bad.append(("u form", tag))
                    else:
                        N = n1 + n2
                        if N <= 2 and u < 0: bad.append(("uc<0", tag))
                        if N >= 3 and u != 2 * K - 2 * fB: bad.append(("uc form", tag))
                        if u < 4 - 2 * K: bad.append(("uc low", tag))
print("violations:", len(bad)); print(bad[:10])
