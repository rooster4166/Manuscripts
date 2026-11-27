# A19 — Referee audit: near-dirac §§8–9 (one-apex balancing; Scheduling Hypothesis; conditional reduction)

Auditor: independent adversarial referee pass, 2026-11-27.

Sources audited:
- **[ND]** `manuscripts/near-dirac/near-dirac.tex`, §8 (lines 528–640) and §9 (lines 642–740). I did not edit the manuscript.
  - Text audited: branch `claude/audit-a19`, which equals `origin/claude/quirky-dirac-d9km1q` at **3e70a9c** (it contains 4343cd0).
  - The .tex was last changed in **cb67ee6**; 4343cd0 changed only the README and `connections.md`.
  - The PDF (21 pp., created 04:36:33 UTC, which is the cb67ee6 commit time) matches the .tex.
  - Numbers are those of the compiled PDF: Lemma 8.1 (`lem:bal-exact`), Lemma 8.2 (`lem:bal-robust`), Proposition 8.3 (`prop:bal-app`), Remark 8.4 (`rem:bal-scope`), Problem 8.5 (`prob:counting`), Definition 9.1 (`def:SH`), Remark 9.2 (`rem:SH`), Theorem 9.3 (`thm:conditional`), Problem 9.4 (`prob:intermediate`).
- **Context only, not re-audited.** §§1–7 (Theorem 1.1, Lemma 4.1) and `research/audit/A17-near-dirac.md`.
- **SP** = `gallai/02-november-25/separating-pairs.pdf` §14, via pdftotext. I read:
  - Cor 14.24 (p. 158) and Cor 14.26 (p. 162);
  - §14.18's obstruction (p. 165);
  - Thm 14.31 and its proof (pp. 165–167);
  - Thm 14.33 and Lemma 14.34 (pp. 168–170);
  - Thm 14.37 and its proof (pp. 170–171);
  - Cors 14.38 and 14.39 (p. 171).

  pdftotext drops the square roots in the choice of q of 14.31 and 14.33. I checked them on the rendered page: "e + √(m(h+1)) = o(q)".
- `manuscripts/near-dirac/README.md` lines 42–48 and `research/connections.md` lines 141–144, where they restate §§8–9.

**Independence.** No scripts accompany §§8–9. Everything in `research/audit/A19-scripts/` was written from the text of ND alone.
- `a19_balance.py` covers §8:
  - Lemmas 8.1 and 8.2: the proofs' constructions, run on 20,000 random and extremal instances;
  - graph-level instances, with explicit neighbourhoods, edges inside X, and an adversarial choice of W;
  - the exact identity;
  - the sweep of Prop 8.3(i);
  - the regime of Problem 8.5;
  - the (H2) counterexample.
- `a19_params.py` covers the constants of Prop 8.3(ii) and the parameter choices of Theorem 9.3.

Outputs are in `A19-scripts/out/`.

Verdicts: **SOUND**; **GAP** (fixable; the fix is stated); **ERROR** (false; the false statement is identified); **UNCLEAR** (cannot be settled from the available material).

Throughout, "healthy degree" d_x = α_x + β_x is the degree of x into healthy vertices, as Prop 8.3 prescribes ("Take the degrees α_x, β_x into the healthy vertices"). d_X(x) is the number of neighbours of x in X. Healthy internal edges are cleared, as in the route of §8. So e_R(I) − e_R(K) = e_X(I) − e_X(K∖W).

---

## 0. Summary table

| # | Item | Verdict | Note |
|---|---|---|---|
| P1 | §8 route: the one-apex window (eq. `window`) from Lemma 4.1 | **SOUND**; nit | With b′ ∈ {0,1} and b′(V(R)) = D: 2(e_R(I) − e_R(K)) = tD + b′(K) − b′(I), and b′(K) − b′(I) ranges over {−D, −D+2, …, D}. Nit: t = ±2 is also compatible with CKLOT's balanced parts (apex on the smaller side). So t ∈ {−1, 0, 1} is a choice, not forced. §1. |
| P2 | \|W\| = \|K_H\| − \|I_H\| + \|X_K\| − \|X_I\| + t | SOUND | Direct count. |
| P3 | Abstract problem: S, Γ, validity, and the mirror (S, Γ) ↦ (−S, −Γ) | SOUND | A first-order model. Its two omissions (edges inside X, edges X_K–W) are stated. |
| P4 | **Lemma 8.1** (exact balancing) | **SOUND**; nit | All four cases check. "S_r < S_{r−1} + 2D" should read "≤". 20,000 instances, 0 failures. §2. |
| P5 | **Lemma 8.2** (robust, μ ≤ D/8) | **SOUND** | The five cases are exhaustive. The same case analysis allows μ ≤ D/4, and a one-vertex instance breaks it at μ = D/4 + 1. 0 failures at D/8 and at D/4. §2. |
| P6 | Prop 8.3, statement | GAP (minor) | The bound d_x − \|N(x) ∩ W\| ≥ D is stated only for the interval shore. It holds for every x ∈ X, and Thm 9.3 needs it for every x (H2). \|K_H\| ≥ \|Δ\| + s + 1 is used but not stated. §3.1. |
| P7 | **Prop 8.3(i)** (monotone sweep) | **GAP**: three intermediate claims are false; the conclusion is true | Edges inside X **raise** F; they do not lower it. The step is d_{x_r} + d_X(x_r) − \|N(x_r) ∩ W_{r−1}\| − e(X_K, returned pair). The claims "the change is also at most d_{x_r}", "≤ 5D/4" and "F(r) ∈ [−D, D/4)" are false. Script: 1,335 steps exceed d_{x_r}, 703 exceed 5D/4, and an explicit instance has F(r) = 118 ≥ D/4 = 100. The conclusion survives: F(r) < D/4 + s and D/4 + 3s ≤ D. §3.3. |
| P8 | Prop 8.3(ii) (via Lemma 8.2) | **SOUND**; nit | The error bound e(G[X]) + e(X_K, W) is right. The chain "≤ 3s² + 3 ≤ D/8" is false for s = 0 with D < 24 and for s = 1 with 36 ≤ D ≤ 46. Use 5s²/2 + s ≤ 9s²/2 ≤ D/8 (s ≥ 1). §3.4. |
| P9 | Remark 8.4 | GAP (wording) | "Neither Lemma 8.2 nor the monotone argument of part (i) applies" is superseded: a two-sided monotone argument does apply (P11). A weak site placed on its cross side may have only ≈ q = o(n) neighbours on the other shore, not "a small linear fraction". §4.4. |
| P10 | **Problem 8.5: the identity for E** | **ERROR** | With the convention of Prop 8.3, the exact value is **S + e(G[X_I]) − e(G[X_K]) + e(X_K, W)**. The printed signs of the two X–X terms are reversed: 13,536 of 16,606 configurations disagree, and a two-vertex example gives exact = 21, printed = 19. The printed formula is right only if α, β are full, placement-dependent degrees, which is not the abstract problem's S. The bound \|E\| ≤ C(s,2) + s(2s+1) is **SOUND** for either sign. README l. 46 repeats the error. §4.1. |
| P11 | **Problem 8.5: status "open"** | **ERROR (status)**: it has an affirmative solution | **A19 Proposition P** (§4.2), a two-sided sweep, gives an *exactly* valid configuration under the standing hypotheses of Prop 8.3, **without (i) or (ii)**. No tolerance is needed. Checks: 1,500/1,500 adversarial instances in the Problem 8.5 regime, where Lemma 8.2 with an adversarial W fails 620 times; 800/800 in regime (ii); 150/150 small instances against exhaustive search. |
| P12 | **Definition 9.1 (SH)** | **SOUND** (well-posed); nits | The sequence formulation is standard and has no quantifier issue. The hypotheses are consistent with the necessary condition from Lemma 4.1. Nits: "b(V) ∈ {2⌊n/2⌋, n}" means b(V) = 2⌊n/2⌋ by parity; (H1) lacks SP's "+1" in √(m(h + r + 1)), which is harmless because h = 0 forces X = ∅. §5.1. |
| P13 | **Remark 9.2** (SH with X = ∅ is SP's regime) | SOUND on unequal shores; GAP (wording) | The quote is verbatim, but it is the *penultimate* sentence of SP's proof, not the last. SH(X = ∅) also contains equal shores with \|b(I) − b(K)\| up to o(q). Neither SP's sentence ("on unequal shores") nor SP 14.27 (\|b(A) − b(B)\| ≤ 2) covers that case, but ND Theorem 1.1 with X = ∅, ρ = 0 does. The sentence about W is moot, since SH's conclusion does not involve W. §5.2. |
| P14 | Thm 9.3: parameters (q ≈ ξ^{1/5}n, ω = ξ^{−1/100}) | SOUND choice; **GAP** | The displayed inequality holds for ξ ≤ 8.2·10⁻⁵, and every (H1) ratio tends to 0. A lower bound on ξ_n is needed and not stated: ω_n is undefined at ξ_n = 0, and n\|W\| = o(q²) fails when \|W\| = 1 and ξ_n ≤ n^{−5/2}. Fix: without loss of generality ξ_n ≥ 1/log n. §5.4. |
| P15 | Thm 9.3: sizes, healthy vertices, (B1), hypotheses of Prop 8.3 | SOUND | \|X\| ≤ 4ξn²/q = o(q); \|Δ_H\| = o(q); mis ≤ 3ξn + λ; d_x ∈ [D + \|Δ_H\| + 2\|X\| + 2, 5D/4]. |
| P16 | **Thm 9.3: "(H2) holds"** | **GAP** | (H2) bounds \|N(x) ∩ I\| and \|N(x) ∩ K\| over *all* neighbours. The proof only gives *healthy* degrees ≤ D. Edges inside X can reach D + \|X\| − 1 when x is placed on its cross side. The script's Prop 8.3(i) output has \|N(x₀) ∩ I\| = 401 > D = 400. Fix: shift the threshold of X by σ_n = ⌈4ξ_n n²/q_n⌉ + 1 = o(q_n). §5.5. |
| P17 | Thm 9.3: (H3), (H4) | SOUND | (H3) is the definition of \|W\|. (H4) is exactly the conclusion of Prop 8.3 (exact control of e_X(I) − e_X(K∖W)). |
| P18 | Thm 9.3: (H1) | SOUND, given the fix of P14 | h ≤ 2λ + 3ξn + \|X\|; n·h, n\|X\|, n\|W\| = o(q²); e ≤ ξn. |
| P19 | Thm 9.3: profile and contradiction | SOUND; GAP (logic, minor) | The profiles are right at both parities, and the private leaf is appended at t₀. SH is asymptotic, so the contradiction must run along the subsequence on which the conclusion fails, not "for some large n". §5.6. |
| P20 | Thm 9.3: exhaustiveness and inputs | SOUND | ¬(b) ⟺ (i) ∨ (ii). The proof uses Prop 8.3, SH, SP 14.24, SP 14.26 and the proof of SP 14.39. Theorem 1.1 is **not** used and not needed. With P11, alternative (b) can be **deleted**. §5.7. |
| P21 | Problem 9.4 | SOUND as a problem; GAP (wording) | At the lower end of its range, own = λ_n = q²/(nω_n) is itself o(q²/n), so "too far from bipartite for SP's scheduling" is not literally true there. "Cannot keep all its internal edges on the bin shore" holds only on its larger side. §5.8. |
| P22 | SP descriptions in §§8–9 | **SOUND**; nits | Checked: 14.24, 14.26, 14.31/14.33 (interval, bins, labelled pairs, removed W), 14.34 (queue), 14.37 (clearing and the quoted sentence), 14.39 (bounds on the cut), and SP's tolerance h = o(q²/n). Nits: 14.31 has no labelled pairs, and its bin shore is B (L is the name in 14.33). §6. |
| P23 | README ll. 44–48; `connections.md` ll. 141–144 | GAP (doc) | They repeat P10's sign, the "open" status and alternative (b). |

**Overall.**

*What is correct.*
- **Lemmas 8.1 and 8.2 are correct.**
- **Proposition 8.3 is correct as stated**, though the proof of part (i) uses three false intermediate bounds (P7), which the slack absorbs.
- **The Scheduling Hypothesis is a well-posed open statement.** For X = ∅ it is the regime of SP's unequal-shore construction together with ND Theorem 1.1 at equal shores.
- **Theorem 9.3 follows from Proposition 8.3 and SH** once three gaps are closed: the (H2) count with edges inside X (P16), a lower bound on ξ_n (P14) and the subsequence form of the contradiction (P19). All three fixes are short.
- The SP descriptions are accurate.

*What is wrong.*
- The **identity in Problem 8.5 has the wrong sign** on the X–X terms (P10). The same slip causes P7.
- **Problem 8.5 is not open.** Proposition P, a two-sided sweep, meets the window *exactly* whenever |Δ| + 5s + 1 < D and D + |Δ| + 2s + 2 ≤ d_x ≤ 5D/4.

*Consequence.* Hypotheses (i)/(ii) can be dropped from Prop 8.3, and alternative (b) from Theorem 9.3. **Under SH, every failure sequence with Δ ≤ (1/2 + o(1))n has, at all large n and for every maximum cut, an intermediate vertex** λ_n ≤ own(v) < d(v) − D_n + σ_n.

---

## 1. The route and the window (lines 530–553)

**The window.** Lemma 4.1 holds for every integer ρ (A17 N8). Apply it with A := I ∩ V(R), B := K ∩ V(R) and ρ = −t:

2(e_R(I) − e_R(K)) = tD + b′(K) − b′(I).

With one apex, b′ ∈ {0,1} and b′(I) + b′(K) = D. So b′(K) − b′(I) = D − 2b′(I) runs over {−D, −D + 2, …, D}. This gives (eq. `window`), and conversely every integer value in the window is attained, since D is even. **SOUND.**

**Nit (t = ±2).** CKLOT 1.3.5 needs a part of size ⌊N/2⌋ (N = |V(R)| + 1) spanning ≤ ε_ex N² edges, and likewise its complement. If |I ∩ V(R)| = k + 2 and |K ∩ V(R)| = k, put the apex in K. Then the parts have sizes k + 2 and k + 1 = ⌊(2k + 3)/2⌋, and e_J(K + apex) = e_R(K) + b′(K) is small. So t = 2 (and symmetrically t = −2) is admissible, with window [D/2, 3D/2] (resp. [−3D/2, −D/2]). The text reads "t := … ∈ {−1, 0, 1}" as if it were forced. It is a restriction, harmless for sufficiency.

**|W|.** |I ∩ V(R)| = |I_H| + |X_I| and |K ∩ V(R)| = |K_H| − |W| + |X_K|, which gives the stated formula. **SOUND.**

**Abstract problem.** For naming ν = B, (ι, κ) = (α, β) and Δ_ν = Δ; the mirror swaps them. The slack Γ satisfies |W| = Γ + t. S is the first-order value of e_X(I) − e_X(K∖W): it omits edges inside X and the edges X_K–W, as the text says. **SOUND.**

---

## 2. Lemmas 8.1 and 8.2

**Lemma 8.1.**
- S_r − S_{r−1} = d_{x_r} ∈ [D, 2D], S_0 = −Σβ ≤ 0 ≤ Σα = S_s, and Γ_r = Δ + s − 2r.
- For the least r with S_r ≥ −D:
  - either r = 0 and S_0 ∈ [−D, 0];
  - or S_r ≤ S_{r−1} + 2D < D. The text writes "<" for the first inequality; nit.
- The mirror (A, X∖M_r) has imbalance −S_r and slack −Γ_r.

The four cases:

| S_r | Γ_r | configuration | Γ + t | window |
|---|---|---|---|---|
| [−D, 0] | ≥ 1 | (B, M_r, −1) | ≥ 0 | [−D, 0] ∋ S_r |
| [−D, 0] | ≤ 0 | (A, X∖M_r, 1) | −Γ_r + 1 ≥ 1 | [0, D] ∋ −S_r |
| (0, D) | ≥ −1 | (B, M_r, 1) | ≥ 0 | [0, D] |
| (0, D) | ≤ −2 | (A, X∖M_r, −1) | ≥ 1 | [−D, 0] ∋ −S_r |

**SOUND.**

**Lemma 8.2.** Take the least r with S_r ≥ −3D/4. The steps are ≤ 5D/4, so S_r ∈ [−3D/4, D/2). Each of the five cases places [S − μ, S + μ] in its window when μ ≤ D/8. The tightest constraints are:
- the t = −1 case: −3D/4 − μ ≥ −D;
- the t = 0 cases: 2μ ≤ D/2.

Both hold for every **μ ≤ D/4**, so the lemma is true with D/4. This is not claimed, and nothing needs it.

The case split (S_r ≤ 0 with Γ_r ≥ 1 or ≤ 0; S_r > 0 with Γ_r ≥ 0, = −1 or ≤ −2) is exhaustive. Lemma 8.2 does not use the lower bound d_x ≥ D at all.

`a19_balance.py` [A]:
- 20,000 instances: D from 2 to 1000, s ≤ 25, Δ ∈ [−3s − 3, 3s + 3]; 30% with every step exactly D or 2D (resp. 5D/4).
- **0 failures** for Lemma 8.1, for Lemma 8.2 at D/8, and at D/4.
- The instance D = 400, s = 1, α = 0, β = 300 is robust at μ = 100 and not at μ = 101.

**Both SOUND.**

---

## 3. Proposition 8.3

### 3.1 Statement

- The cross-edge bound follows from |W| = Γ + t ≤ |Γ| + 1 ≤ |Δ| + s + 1 and d_x ≥ D + |Δ| + 2s + 2. It holds for **every** x ∈ X, not only those on the interval shore. Theorem 9.3's (H2) asks for it at every x; say "every vertex of X".
- The sweep needs |K_H| ≥ |Δ| + s + 1 healthy bin-shore vertices. This is automatic in every application but unstated. **GAP (minor).**

### 3.2 The exact value

Write X_I and X_K for the exceptional vertices on the two shores. Since healthy internal edges are cleared, every internal edge of R at X is of one of two kinds: x–(healthy vertex), counted once in ι_x or κ_x, or x–y with x, y ∈ X on the same shore. So

  e_X(I) = Σ_{X_I} ι_x + e(G[X_I]),  e_X(K∖W) = Σ_{X_K} (κ_x − |N(x) ∩ W|) + e(G[X_K]),

and therefore

  **(★)  e_X(I) − e_X(K∖W) = S + e(G[X_I]) − e(G[X_K]) + e(X_K, W).**

`a19_balance.py` [B1] checks (★) in all 16,606 configurations of 300 random instances (all namings, all M, all t, random W).

### 3.3 Part (i): three false intermediate claims; the conclusion holds

**The step.** Move x_r from K to I, and return two vertices w, w′ of W to the bin shore. By (★):

  F(r) − F(r−1) = d_{x_r} + d_X(x_r) − |N(x_r) ∩ W_{r−1}| − e(X_K^{(r)}, {w, w′}).

An edge x_r y with y ∈ X_I turns from cross into I-internal (+1). An edge x_r y with y ∈ X_K turns from K-internal into cross, which also gives +1 to the difference. So the X–X edges contribute **+d_X(x_r) ∈ [0, s − 1]**. The proof instead counts them as "at most 2s" *subtracted*, and concludes "the change is also at most d_{x_r}". That is false.

- *Lower bound.* The paper's "0 < F(r) − F(r−1)" survives: the true step is ≥ d_{x_r} − |Δ| − 3s − 1 > 0.
- *Upper bound.* The true bound is F(r) − F(r−1) ≤ d_{x_r} + s − 1 ≤ 5D/4 + s − 1. So "≤ 5D/4" and "F(r) ∈ [−D, D/4)" are false.

**Counterexample** (`a19_balance.py` [B2b]):
- D = 400, s = 20, Δ = 21, X a clique;
- α_x = 204 and β_x = 296, so d_x = 500 = 5D/4;
- W taken from healthy vertices with no X-neighbours.

Then F(11) = −401 and F(12) = 118 ≥ D/4. The step is 519 > 5D/4.

Over 1,302 random instances [B2]:
- 1,335 steps exceed d_{x_r} (by up to 23, against the bound s − 1);
- 703 steps exceed 5D/4.

**The conclusion still holds.**
- The least r with F(r) ≥ −D has F(r) ∈ [−D, D/4 + s − 1).
- If F(r) ≤ 0, t = −1.
- Otherwise use t = 1 with two more removed vertices. F then lies in (0, D/4 + 3s − 1] ⊆ [0, D], because 5s + 1 < D gives 3s < 3D/4.

The conclusion is met exactly in 1,302/1,302 runs [B2], and in the counterexample (t = 1, value 118). **GAP: the intermediate bounds are wrong; the conclusion is right.** Fix F2 (§7).

The same sign slip appears in the identity of Problem 8.5 (§4.1).

### 3.4 Part (ii)

**The error.** True value − S = e(G[X_I]) − e(G[X_K]) + e(X_K, W) by (★). Its absolute value is ≤ e(G[X]) + e(X_K, W) ≤ C(s, 2) + s(|Γ| + 1). When |Δ| ≤ s, |Γ| ≤ 2s. So the error is ≤ s²/2 + s(2s + 1) = 5s²/2 + s. **SOUND.**

The parenthetical "counted … twice or not at all in S" is loose. With healthy degrees, an X–X edge on one shore is counted *zero* times in S.

**The chain "≤ 3s² + 3 ≤ D/8".** It needs 24s² + 24 ≤ D. With s ≤ √D/6 this fails:
- for s = 0 and D < 24, harmless since the error is then 0;
- for s = 1 and 36 ≤ D ≤ 46: 6 > D/8.

The needed bound does hold everywhere. For s ≥ 1 we have D ≥ 36s², so 5s²/2 + s ≤ 9s²/2 ≤ D/8. `a19_params.py`: 17 pairs (s, D) with D ≤ 20,000 break the printed chain, and 0 break the needed bound. **SOUND (nit).**

`a19_balance.py` [B3]: in regime (ii), Lemma 8.2's configuration with the *most adversarial* W meets the window exactly in 800/800 instances. The largest |exact − S| is 53.

---

## 4. Remark 8.4 and Problem 8.5

### 4.1 The identity in Problem 8.5: ERROR

Problem 8.5 prints the exact value as S − e(G[X_I]) + e(G[X_K]) + e(X_K, W), i.e. E = −e(G[X_I]) + e(G[X_K]) + e(X_K, W). By (★), the correct value is

  **E = +e(G[X_I]) − e(G[X_K]) + e(X_K, W).**

**A two-vertex example** [B1]:
- X = {x, y}, with xy an edge;
- both on I = A;
- α = (10, 10).

Then e_X(I) − e_X(K) = 21 and S = 20, but the printed formula gives 19. Over all 16,606 configurations of [B1], the printed formula is wrong in 13,536.

**Where the sign comes from.** The printed formula is correct if ι_x = |N(x) ∩ I| and κ_x = |N(x) ∩ K| are *full* degrees on the *placed* shores. Then each edge inside X_I is counted twice in S. But those degrees depend on the placement M, so S would no longer be the imbalance of the abstract problem, where α_x and β_x are fixed integers. Prop 8.3 explicitly uses healthy degrees. Under that convention the printed formula is wrong.

**The bound.** |E| ≤ C(s,2) + s(2s+1) holds for either sign: |e(G[X_I]) − e(G[X_K])| ≤ C(s,2) and 0 ≤ e(X_K, W) ≤ s|W| ≤ s(2s+1). **SOUND.**

**Order s².** "It can be of order s², for example when every exceptional vertex is adjacent to most of the healthy bin shore" is correct.

README line 46 repeats the wrong E.

### 4.2 Problem 8.5 has an affirmative answer: A19 Proposition P

**Proposition P.** Assume the hypotheses of Prop 8.3 *other than* (i)/(ii):
- s = |X|, Δ = |B_H| − |A_H|, |Δ| + 5s + 1 < D;
- for every x, the healthy degrees satisfy (B1) and D + |Δ| + 2s + 2 ≤ d_x ≤ 5D/4;
- |A_H|, |B_H| ≥ |Δ| + s + 1.

Then there are a naming, a placement of X, t ∈ {−1, 0, 1} and a set W of healthy bin-shore vertices, with |W| = Γ + t ≤ |Δ| + s + 1, such that the **exact** value e_X(I) − e_X(K∖W) lies in [D(t−1)/2, D(t+1)/2]. In particular d(x) − |N(x) ∩ W| ≥ D for every x ∈ X.

**Proof.**

*Setup.* Order X = {x_1, …, x_s}. At stage r, put x_1, …, x_r on A and the rest on B (healthy vertices stay put). Write:
- Γ_r = Δ + s − 2r, which is |B| − |A| at stage r;
- C_r = e_X(A) − e_X(B) at stage r, with nothing removed.

As in §3.3:
- C_0 = −e_X(B) ≤ 0 ≤ e_X(A) = C_s;
- C_r − C_{r−1} = d_{x_r} + d_X(x_r) ≤ 5D/4 + s − 1 < 2D.

For a given stage r both namings are available:
- **Bin B** (interval A, M = {x_1, …, x_r}). Here |W| = Γ_r + t, W ⊆ B_H, and the exact value is C_r + e(X_B, W) ≥ C_r.
- **Bin A** (interval B, M = {x_{r+1}, …, x_s}). Here |W′| = −Γ_r + t, W′ ⊆ A_H, and the exact value is −C_r + e(X_A, W′) ≥ −C_r.

1. **Sweep with bin B** over R_B = {r : Γ_r ≥ 1}, an initial segment.
   - Fix a list w_1, w_2, … of B_H and put W_r = {w_1, …, w_{Γ_r − 1}}. These sets are nested and decrease with r.
   - F_r = C_r + e(X_B^{(r)}, W_r) is the exact value of (B, M_r, −1, W_r).
   - F_0 = −e_X(B∖W_0) ≤ 0, and F_r − F_{r−1} ≤ C_r − C_{r−1}, since X_B and W both shrink.
   - If some r ∈ R_B has F_r ≥ −D, the least such r has F_r < −D + 5D/4 + s − 1 = D/4 + s − 1 (or r = 0 and F_0 ∈ [−D, 0]).
   - Then use t = −1 if F_r ≤ 0. Otherwise use t = 1 with w_{Γ_r}, w_{Γ_r+1} added; the value is then in (0, D/4 + 3s) ⊆ [0, D].
2. **Sweep with bin A** over R_A = {r : Γ_r ≤ −1}, from r = s downwards. This is symmetric, with F′_r = −C_r + e(X_A^{(r)}, W′_r), |W′_r| = −Γ_r − 1 and F′_s = −e_X(A∖W′_s) ≤ 0. If it fails, C_r > D on all of R_A.
3. **If both sweeps fail.** Then C_r ≤ F_r < −D on R_B and C_r ≥ −F′_r > D on R_A.
   - **Γ never 0, i.e. Δ + s odd or |Δ| > s.**
     - If R_B = ∅, then Γ_0 ≤ −1, so R_A = [0, s]. The bin-A sweep reaches r = 0, where F′_0 = −C_0 ≥ 0, so it does not fail.
     - Likewise if R_A = ∅.
     - Otherwise max R_B + 1 = min R_A, because Γ goes from 1 to −1. Then C jumps by more than 2D in a single step, which contradicts C_r − C_{r−1} < 2D.
   - **Γ_{r₀} = 0 for some r₀.**
     - If r₀ ≥ 1, then r₀ − 1 ∈ R_B, so C_{r₀} < −D + 5D/4 + s = D/4 + s. If r₀ = 0, C_0 ≤ 0.
     - Symmetrically C_{r₀} > −D/4 − s.
     - Since s < D/5, |C_{r₀}| < D/2. So (B, M_{r₀}, t = 0, W = ∅) is valid: Γ + t = 0, and the value C_{r₀} lies in [−D/2, D/2], with no error at all.

In every case |W| ≤ max_r |Γ_r| + 1 ≤ |Δ| + s + 1. ∎

**What makes it work.** The paper's argument goes wrong at the mirror step of Lemma 8.2, where W has size up to 2s + 1 and contributes uncontrolled error. P avoids this in two ways:
- each sweep tracks the *exact* value with nested W, so the edges X_K–W are part of a one-sided monotone quantity rather than an error term;
- the only stage at which neither sweep applies has Γ = 0, where t = 0 and W = ∅.

Only d_x ≤ 5D/4 and s < D/5 are used for the counting. The lower bound on d_x is used only for the cross-edge condition.

### 4.3 Verification of Proposition P

`a19_balance.py`, [B3/4] and [B4b]. The two-sided sweep was run with the most adversarial W: the healthy bin-shore vertices with the most X-neighbours are removed first.
- **Problem 8.5 regime** (|Δ| ≤ s, √D/6 < s ≤ (D/4 − 2)/3, D ∈ {400, …, 3200}): 1,500 instances. 70% are structured so that every removed vertex is adjacent to all of X_K, and the density of edges inside X is 0, ½ or 1.
  - The paper's route fails here: Lemma 8.2's configuration with an adversarial W **misses the window in 620**, with |exact − S| up to 33,113.
  - **Proposition P returns an exactly valid configuration in 1,500/1,500.** The branches used: sweep B 768, sweep A 729, zero stage 3.
- **Regime (ii):** 800/800.
- **Small instances** (s ≤ 8, X a clique, d_x = 5D/4): in 150/150, exhaustive search over all (ν, M, t) finds a valid configuration and P returns one.

### 4.4 Remark 8.4

- **First bullet.** "Which holds once vertices with min(d_A, d_B) ≤ d − D have had their few internal edges cleared" passes over the intermediate vertices, whose internal edges are not few. Problem 9.4 later names them. Wording.
- **"The remaining counting case … neither Lemma 8.2 nor the monotone argument of part (i) applies."** This is true of the one-sided argument as written, but the case is not open: see §4.2.
- **Weak sites.** "Whose neighbours on the other shore may be a small linear fraction of that shore" is too optimistic. A vertex placed on its *cross* side has, as cross neighbours, its original own-side neighbours, which may number only own(x) ≈ d − D ≈ q = o(n). The balancing lemmas do place vertices on their cross side: M_r takes x_1, …, x_r regardless of their sides. So a weak site may have ≈ q neighbours across and spend almost all of them (2p_x = d − D − |N(x) ∩ W|). This matters for SH's scheduling half. **GAP (wording).**

---

## 5. Section 9

### 5.1 Definition 9.1 (SH): well-posed

**Quantifiers.** SH says: for every sequence of data (G, I, K, X, W, t, D, b) with n → ∞ satisfying (H1)–(H4), every sufficiently large member decomposes into b(V)/2 paths realising b.
- This is the compactness form SP itself uses ("along a family").
- It is equivalent to a uniform finite statement with functions in place of the o(·)'s.
- There is no hidden quantifier: D, t, W, X are data, and the conclusion involves none of them.

**SOUND.**

**Consistency checks.**
- **(H4) is the necessary condition.** Take a one-apex finish in which X keeps all its internal edges, healthy internal edges are cleared, and V(R) = I ∪ (K∖W). By §1, (H4) is exactly the condition from Lemma 4.1 for that finish. (H3) is the CKLOT balance with t ∈ {−1, 0, 1}.
- **(H1) matches SP's tolerances.** SP 14.31 needs e + √(m(h+1)) = o(q). SP 14.33 needs e + r + √(m(h + r + 1)) = o(q), with r = |W|. (H1) is the same up to the "+1".
- **The missing "+1" is harmless.** If h = 0, every healthy vertex of K is adjacent to every vertex of I, including X_I. Then |N(x) ∩ K| ≥ |K_H| > D for x ∈ X_I, contradicting (H2), so X_I = ∅; likewise X_K = ∅. With X = ∅, D does not enter SH, so it can be enlarged. If h ≥ 1 or |W| ≥ 1, (H1) itself forces q ≫ √n.
- **No obvious counterexample.** The hypotheses force each exceptional vertex to miss ≥ |K_H| − D ≈ q opposite healthy vertices. Summing, |X|·q ≲ n·h/2. So |X| = o(q) is already implied by n·h = o(q²); (H1) is consistent. I found no configuration satisfying (H1)–(H4) for which a decomposition is impossible.
- **The profile constraint.** "b(V) ∈ {2⌊n/2⌋, n}": b(V) ≡ Σd ≡ 0 (mod 2), so at odd n the value n is impossible, and the condition is just b(V) = 2⌊n/2⌋. Nit.
- **(H2)'s d(x) ≤ 5D/4** serves only the robust lemma. With Proposition P it is still needed (for the step bound), and it is harmless.

### 5.2 Remark 9.2: SH with X = ∅

- **The quote is verbatim** (SP p. 171): "The same construction realizes any cap-two profile of the degree parity on unequal shores when the number of even-degree sites and the three size and degree errors are o(m)." It is the **penultimate** sentence of the proof; the final one is "Extend a row ending at the true root if required."
- **SH(X = ∅) is the o(n)-error regime.** With X = ∅, (H2) and (H4) are vacuous, since 0 lies in every window for t ∈ {−1, 0, 1}. The hypothesis is then: errors h, e, |W| = o(q), with n(h + |W|) = o(q²). Given any errors that are o(n), choosing q = n·ε^{1/3}, where ε = (h + e + |W| + 1)/n, satisfies (H1). So SH(X = ∅) is exactly "o(n) size, degree and parity errors ⇒ every profile with b(V) = 2⌊n/2⌋ is realised".
- **Unequal shores.** This is SP's claim, which follows from 14.33 after the internal edges are cleared, as in the proof of 14.37. **SOUND.**
- **Equal shores.** |K| = |I| occurs when |W| = t ∈ {0, 1}. Here SH(X = ∅) allows |b(I) − b(K)| up to e = o(q). SP's sentence is restricted to "unequal shores", and SP 14.27 needs |b(A) − b(B)| ≤ 2. This sub-case is covered instead by **ND Theorem 1.1** with X = ∅, ρ = 0, own, mis ≤ cm and |b(A) − b(B)| ≤ e ≤ cm. **GAP (wording):** say so.
- **"SP chooses its removed set itself; in SH, W is prescribed …".** For X = ∅, SH's conclusion does not involve W, so SP may ignore the prescribed W. The sentence is moot. SP's own |W| corresponds to t = −1.
- **The intended proof of SH** (one-apex construction, blocks u′ x w u, o(q) blocks per slot) is a plausible plan, not a claim. Per slot there are ≈ |X|·(q/2)/(n/4) = O(|X|q/n) = o(q) exceptional visits. Consistent.

### 5.3 Theorem 9.3, step by step

| Step | Claim | Check | Verdict |
|---|---|---|---|
| Parameters | ξ_n → 0, uniform over maximum cuts: \|\|A\| − \|B\|\| ≤ ξn and e(A) + e(B) ≤ ξn²; degrees in n/2 ± ξn; ≤ ξn even-degree vertices | The cut bounds come from the proof of SP 14.39, via 14.26: (a − b)²/4 ≤ n²/4 − M and Σd_in = 2(\|E\| − M), uniformly. Degrees: δ ≥ n/2 − o(n) is the definition in SP 14.24; the upper bound is the hypothesis on Δ. Parity: SP 14.26, since Δ ≤ (1/2 + o(1))n gives odd = n − o(n). Wording nit: "the first two items use the proof of SP 14.39"; only the first does. | SOUND |
| q_n, ω_n, λ_n | q ≥ ω(ξ^{1/3} + ξ^{1/4})n; λ = q²/(nω) ≥ ωξ^{1/2}n ≫ ξn | Correct. The example q = ξ^{1/5}n, ω = ξ^{−1/100} satisfies the inequality iff ξ ≤ 8.2·10⁻⁵ (`a19_params.py`), so for large n. A lower bound on ξ_n is missing (§5.4). | SOUND / GAP |
| Sizes | own(x) ≥ q − 2ξn ≥ q/2, so \|X\| ≤ 4ξn²/q = o(q); \|Δ_H\| ≤ ξn + \|X\| = o(q) | o(q) needs q ≫ ξ^{1/2}n, which holds. | SOUND |
| Healthy vertices | ¬(a) ⇒ own < λ; mis ≤ max(\|A\|, \|B\|) − d + own ≤ 3ξn + λ | (1.5ξn suffices.) | SOUND |
| Exceptional vertices | max(d_A, d_B) = cr ≤ D (maximum cut ⇒ own ≤ cr); min ≤ d/2 ≤ D; d ≥ D + q − ξn | (B1) holds for healthy degrees. d_x ≥ D + \|Δ_H\| + 2\|X\| + 2 since q ≫ \|Δ_H\| + 3\|X\| + ξn. d ≤ n/2 + ξn ≤ 5D/4 for large n. \|Δ_H\| + 5\|X\| + 1 < D. | SOUND |
| Placement | ¬(b) ⇒ (i) or (ii) ⇒ Prop 8.3 applies; (H3) and (H4) hold | (H3) by \|W\| = Γ + t. (H4) is the Prop's exact conclusion. | SOUND |
| (H2) | "(H2) holds" | Only the healthy degrees are bounded by D. Edges inside X can exceed it (§5.5). | **GAP** |
| (H1) | h ≤ 2λ + 3ξn + \|X\|; nh, n\|X\|, n\|W\| = o(q²); e ≤ ξn | Moving X changes own + mis by ≤ \|X\|. nh ≤ 2q²/ω + 3ξn² + 4ξn³/q = o(q²). n\|W\| ≤ ξn² + 2n\|X\| + **n**, and the last term needs q ≫ √n (§5.4). | SOUND given fix |
| Profile | b = 1 on odd vertices. Even n: double half the even vertices, including t₀ if even; b(V) = n. Odd n: double (e₀ − 1)/2; b(V) = n − 1 | Parities correct; b(t₀) ≥ 1; e ≤ ξn. The private leaf is appended to a path ending at t₀. | SOUND |
| Contradiction | "for some large n and some maximum cut … derive a contradiction" | SH is asymptotic (§5.6). | GAP (minor) |

### 5.4 Parameters (`a19_params.py`)

Worst-case ratios with q = ξ^{1/5}n and ω = ξ^{−1/100}, from the proof's own bounds. Each must tend to 0.

| log₁₀ ξ | \|X\|/q | λ/q | h/q | nh/q² | n\|W\|/q² (excluding n/q²) |
|---|---|---|---|---|---|
| −10 | 4.0e−6 | 7.9e−3 | 1.6e−2 | 1.59 | 8.0e−4 |
| −30 | 4.0e−18 | 5.0e−7 | 1.0e−6 | 1.00 | 8.0e−12 |
| −100 | 4e−60 | 1e−21 | 2e−21 | 0.20 | 8e−40 |
| −200 | 4e−120 | 1e−42 | 2e−42 | 0.02 | 8e−80 |

All tend to 0, so the choice is **consistent**.
- nh/q² contains 2/ω = 2ξ^{1/100}, which goes to 0 only very slowly. That is acceptable, since the statement is purely asymptotic.
- The other hypotheses of Prop 8.3, (ξn + 3|X| + |Δ_H| + 2)/q → 0 and d ≤ 5D/4, hold once ξ ≤ 10⁻¹⁰ or so.

**GAP: ξ_n needs a lower bound.** ξ_n is only an upper bound tending to 0, and may be tiny or 0.
- At ξ_n = 0, ω_n = ξ_n^{−1/100} is undefined.
- At ξ_n = n^{−3}, q = n^{2/5} and n/q² = n^{1/5} → ∞. Then X = ∅ (|X| ≤ 4ξn²/q < 1) and |Δ_H| ≤ ξn < 1, so at odd n, |Δ_H| = 1. Lemma 8.2 with s = 0 then returns t = 0 and |W| = 1, and (H1)'s n|W| = o(q²) **fails**.

**Fix:** replace ξ_n by max(ξ_n, 1/log n), which keeps every bound true. Then q ≥ n/(log n)^{1/5} ≫ √n.

Regime (b) is not vacuous a priori: |X| ≤ 4ξ^{4/5}n can exceed √D/6 ≈ 0.12√n.

### 5.5 (H2) with full neighbourhoods: GAP

(H2) bounds |N(x) ∩ I| and |N(x) ∩ K|, which include neighbours in X. It must: x keeps all its internal edges and needs R-degree D − b′(x) ≤ D.

The proof only establishes the healthy bounds α_x, β_x ≤ max(d_A(x), d_B(x)) = cr(x) ≤ D_n. When x is placed on its cross side, together with X-neighbours from its own side:

  |N(x) ∩ I| ≤ cr(x) + |X| − 1,

and this can exceed D_n.

**Example** (`a19_balance.py` [B5]):
- D = 400, s = 6, Δ = 10, which is case (i);
- x₀ and x₁ have α = D, β = 60, and are adjacent;
- x₂, …, x₅ have α = 30, β = D;
- every Prop 8.3 hypothesis holds.

The proof's sweep in the order x₀, …, x₅ gives F = (−1631, −1195, −755, −342, 75, …). The least r with F(r) ≥ −D is 3. The output places x₀, x₁ on I = A, with **|N(x₀) ∩ I| = 401 > D**. In Theorem 9.3's terms: two adjacent exceptional vertices on the same maximum-cut side, each with cr = D_n.

**Fix.** Define

  X := {v : own(v) ≥ d(v) − D_n + σ_n}, σ_n := ⌈4ξ_n n²/q_n⌉ + 1 = o(q_n).

Still own(x) ≥ q/2, so |X| ≤ 4ξn²/q < σ_n. Then cr(x) ≤ D_n − σ_n, and in every placement |N(x) ∩ S| ≤ cr(x) + |X| − 1 < D_n. Alternative (a) becomes λ_n ≤ own(v) < d(v) − D_n + σ_n. Nothing else changes.

### 5.6 The contradiction must run along a subsequence

SH speaks of sequences, so it cannot be applied to "some large n". The correct form:
1. Suppose the conclusion fails for infinitely many n.
2. On that subsequence, pick a maximum cut violating (a) and (b), and the data the proof builds.
3. (H1) holds along the subsequence, because every bound is an explicit function of ξ_n, q_n and ω_n.
4. SH then decomposes G_n for all large members, contradicting failure.

**GAP (logic, minor).**

### 5.7 Exhaustiveness, and what the theorem uses

- ¬(b) ⟺ |Δ_H| ≥ |X| + 1 or |X| ≤ √D_n/6, i.e. (i) or (ii). The dichotomy is exhaustive by construction.
- The proof uses Prop 8.3, SH, SP 14.24 (the definition), SP 14.26 and the proof of SP 14.39.
- **Theorem 1.1 is not used**, and no step needs it. It enters only through Remark 9.2's X = ∅ discussion, at equal shores (§5.2).

**With Proposition P** (§4.2) replacing Prop 8.3, alternative (b) disappears. Under SH, together with the fixes of §§5.4–5.6, every failure sequence with Δ ≤ (1/2 + o(1))n has, for all large n and every maximum cut, a vertex with λ_n ≤ own(v) < d(v) − D_n + σ_n. The summary paragraph (line 740), the README and `connections.md` should then drop "or lie in the open counting regime".

### 5.8 Problem 9.4

The problem is well-posed: handle vertices with λ_n ≤ own(v) < d(v) − D_n. Its heuristic text is loose in two places.
- **"Too far from bipartite for SP's one-apex scheduling. That scheduling needs every site to miss only o(q²/n)".** SP's tolerance is correctly stated, by √(m(h+1)) = o(q). But at the lower end of the range, own = λ_n = q²/(nω_n) is itself o(q²/n). The obstruction is that the bound is not *uniform* once ω_n is fixed, not that each such vertex is out of range.
- **"Its larger side exceeds D, so it cannot keep all its internal edges on the bin shore."** True only when it is placed on its larger (cross) side. On its own side it has own(v) < d − D ≲ q internal edges and could keep them. The next paragraph says as much ("or keep its internal edges").

With Proposition P, the natural next step is P with some vertices *fixed* on their own side. They contribute an offset of up to their own-degree sum to C_r, which breaks C_0 ≤ 0 ≤ C_s when that sum exceeds D. This is where Problem 9.4's counting difficulty actually lies.

---

## 6. SP descriptions used in §§8–9

| Where in ND | Claim about SP | SP text | Verdict |
|---|---|---|---|
| §8 route (l. 532) | interval shore = SP's A in 14.31/14.33 (cyclic intervals; labelled pairs scheduled on it); bin shore = SP's L; W removed as in 14.33 | 14.31 (p. 166): "For a positive site v ∈ A start its cyclic interval…"; B sites in "a cycle of F bins". 14.33 (p. 168): "Choose W ⊂ L of size r and put B = L∖W"; pairs are "labelled internal edge[s] of A", scheduled by Lemma 14.34. | SOUND; nit: 14.31 has no labelled pairs, and its bin shore is B |
| Rem 8.4, Rem 9.2 | healthy internal edges cleared "as in SP 14.37" | 14.37 proof: "We clear all within-shore edges without exhausting these counts … K = 300j … matchings", then Lemma 14.29 | SOUND |
| Rem 9.2 | quoted sentence | verbatim (p. 171); penultimate, not final | SOUND; nit |
| Rem 9.2 | "SP chooses its removed set itself" | "Choose W ⊂ L of size r" (any W) | SOUND |
| Rem 9.2, Rem 8.4 | SP's interval, bin and queue scheduling | 14.31 intervals and bins; 14.33 queue Lemma 14.34 and buckets | SOUND |
| Thm 9.3 | failure sequence "as in SP 14.24" | definition verbatim in ND §2 (A17 N4) | SOUND |
| Thm 9.3 | SP 14.26: odd = n − o(n) when Δ ≤ (1/2 + o(1))n | 14.26: max{Δ, odd} = n − o(n) | SOUND |
| Thm 9.3 | cut bounds from the proof of 14.39 | "(a − b)²/4 = n²/4 − ab ≤ n²/4 − M … Σ d_in(v) = 2(\|E(G)\| − M) = o(n²), uniformly over maximum cuts" | SOUND |
| Prob 9.4 | SP needs h = o(q²/n) | 14.31: e + √(m(h+1)) = o(q); 14.33: e + r + √(m(h + r + 1)) = o(q) | SOUND |

---

## 7. Proposed fixes (not applied; the manuscript is not edited)

- **F1 (P10, Problem 8.5).**
  - Replace the displayed value by "S + e(G[X_I]) − e(G[X_K]) + e(X_K, W)", and E by "e(G[X_I]) − e(G[X_K]) + e(X_K, W)". The bound stands.
  - Alternatively, state that ι, κ are full, placement-dependent degrees; but Prop 8.3 uses healthy degrees.
  - Fix README line 46 likewise.
- **F2 (P7, Prop 8.3(i)).** Replace "the edges from x_r to other exceptional vertices account for at most 2s … The change is also at most d_{x_r}" by:

  > the edges from x_r to other exceptional vertices raise F by d_X(x_r) ∈ [0, s−1], so 0 < F(r) − F(r−1) ≤ d_{x_r} + s − 1 ≤ 5D/4 + s.

  Then:
  - "So the least r … has F(r) ∈ [−D, D/4 + s)";
  - "F ∈ (0, D/4 + 3s] ⊆ [0, D]", since 5s < D.
- **F3 (P8, Prop 8.3(ii)).** "… ≤ C(s,2) + s(2s+1) ≤ 9s²/2 ≤ D/8 for 1 ≤ s ≤ √D/6 (and the error is 0 when s = 0)". Also change "twice or not at all" to "not at all".
- **F4 (P6).** In Prop 8.3: "every vertex of X still has … d_x − |N(x) ∩ W| ≥ D", and add "|K_H| ≥ |Δ| + s + 1" (automatic in Theorem 9.3).
- **F5 (P11). Replace Problem 8.5 by Proposition P (§4.2)**, with its proof, and drop (i)/(ii) from Prop 8.3. Remark 8.4's "remaining counting case" paragraph then goes. The README (ll. 44–46) and `connections.md` (ll. 142–143) should say the counting half is proved in full, under the degree window D + |Δ| + 2s + 2 ≤ d_x ≤ 5D/4 and |Δ| + 5s + 1 < D.
- **F6 (P14, P16, P19, P20, Theorem 9.3).**
  1. "Replacing ξ_n by max(ξ_n, 1/log n) we may assume ξ_n ≥ 1/log n."
  2. Define X with the threshold d(v) − D_n + σ_n, σ_n = ⌈4ξ_n n²/q_n⌉ + 1, and (a) with the same upper limit.
  3. Run the contradiction along the subsequence on which the conclusion fails.
  4. With F5, delete (b). The theorem becomes: *under SH, for all large n and every maximum cut, some v has λ_n ≤ own(v) < d(v) − D_n + σ_n.* Update the summary (l. 740), README l. 48 and `connections.md` l. 144.
- **F7 (P13, Remark 9.2).**
  - "the penultimate sentence of SP's proof of 14.37";
  - add: "At equal shores (|K| = |I|), SH with X = ∅ is ND Theorem 1.1 with X = ∅, ρ = 0, since |b(I) − b(K)| ≤ e = o(q)";
  - drop or reword the sentence about W (for X = ∅, SH's conclusion does not involve W).
- **F8 (P12, SH).** "b(V) = 2⌊n/2⌋" in place of "b(V) ∈ {2⌊n/2⌋, n}".
- **F9 (P9, P21, wording).**
  - Remark 8.4: "may have as few as about q neighbours on the other shore".
  - Problem 9.4: "for the fixed ω_n, such a vertex may miss more than the h = o(q²/n) that SP's scheduling tolerates"; "on its larger side it cannot keep …".
- **F10 (P1, P4, nits).**
  - §8: "t ∈ {−1, 0, 1} (t = ±2, with the apex on the smaller side, would also do)".
  - Lemma 8.1: "S_r ≤ S_{r−1} + 2D < D".
  - Theorem 9.3, Parameters: "the first item uses the proof of SP Corollary 14.39".

---

## 8. Scripts

| Script | What it checks | Output |
|---|---|---|
| `a19_balance.py [seed]` | [A] Lemmas 8.1 and 8.2: 20,000 instances, μ = D/8 and D/4, and the break at μ > D/4. [B1] identity (★) against the printed formula. [B2] Prop 8.3(i): steps against d and 5D/4; conclusion. [B2b] explicit F(r) ≥ D/4. [B3/4] Lemma 8.2 with adversarial W, and Proposition P, in regime (ii) and the Problem 8.5 regime. [B4b] P against exhaustive search. [B5] the (H2) counterexample. | `out/balance.txt` |
| `a19_params.py` | The chain in Prop 8.3(ii); Theorem 9.3's inequality q ≥ ω(ξ^{1/3} + ξ^{1/4})n; worst-case (H1) ratios; the need for a lower bound on ξ_n | `out/params.txt` |

They need Python 3 only. `a19_balance.py` runs in about 3.5 minutes.

---

## 9. Verdict

**§8.**
- **Lemmas 8.1 and 8.2 are SOUND.**
- **Proposition 8.3 is true as stated.** Its part (i) uses three false intermediate bounds that ignore the sign of the edges inside X (P7); the slack absorbs them (F2).
- **Problem 8.5 misstates the error identity** (P10, sign of the X–X terms; the bound is fine).
- **Problem 8.5 is not open:** Proposition P (§4.2), a two-sided exact sweep, meets the one-apex window exactly with no restriction on |Δ| versus |X| (P11).

**§9.**
- **SH is a precisely stated, well-posed open hypothesis.** For X = ∅ it is SP's unequal-shore regime together with ND Theorem 1.1 at equal shores. Remark 9.2 should say the latter (P13).
- **Theorem 9.3 follows from Proposition 8.3 and SH** (Theorem 1.1 is not needed), after three short fixes:
  - (H2) must account for edges inside X (P16: shift the threshold by σ_n = o(q_n));
  - ξ_n needs a lower bound (P14);
  - the contradiction runs along a subsequence (P19).
- With Proposition P, its alternative (b) can be deleted. Under SH, near-regular failure sequences must contain intermediate vertices.
- The SP descriptions are accurate (P22).

No finding affects §§1–7.
