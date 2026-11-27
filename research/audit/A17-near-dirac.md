# A17 — Referee audit: near-dirac ("Exceptional vertices below the Dirac threshold: a balanced return theorem for exact path decompositions")

Auditor: independent adversarial referee pass, 2026-11-27.

Sources audited:
- **[ND]** `manuscripts/near-dirac/near-dirac.tex`. I did not edit the manuscript.
  - **First pass** (§§0–8): branch `claude/quirky-dirac-d9km1q` at 981c46d (merge of d4f66e1), 15 pp. The .tex was last changed in dff7439; the README and `research/connections.md` §D.1 in d4f66e1.
  - **Re-audit** (§9): the author's revision **ebfcdd8** (with 43dcd85), merged into this branch at f01bd3b, 16 pp. This is the **current text**. The verdicts in §§0–8 refer to 981c46d; §9 gives the status of every finding at ebfcdd8 and checks the new material.
  - Numbers such as "Lemma 3.2" are those of the compiled PDF, which match the `\label`s: Theorem 1.1 (`thm:main`), Corollaries 1.2 (`cor:class`) and 1.3 (`cor:failures`), Lemmas 3.1 (`lem:matrix`), 3.2 (`lem:weave`), 4.1 (`lem:identity`), 4.2 (`lem:apex`), Remark 4.3 (`rem:forces`), Lemma 5.1 (`lem:profiles`), Remark 6.2 (`rem:maxcut`), Problems 7.1 and 7.2.
- **External theorems.** `manuscripts/near-dirac/CITATIONS.md`, checked against the arXiv LaTeX sources that I downloaded myself:
  - CKLOT = arXiv:1401.4159v2, file `1factrevision.tex`: §1.3, the definitions at lines 587–595 and Theorem `1factbip` at lines 664–671;
  - GGKO = arXiv:1911.05501v2, file `Introduction.tex`, Theorems `thm:n/2` and `thm:Delta/2`.
- **SP** = `gallai/02-november-25/separating-pairs.pdf` §14 (pdftotext, pp. 158–172): Cor 14.24, 14.26, Thm 14.27 with Lemmas 14.28–14.29, Thms 14.30, 14.31, 14.33, Cor 14.35, Thm 14.37, Cors 14.38 and 14.39. Also Thms 14.1 and 14.5 and Cor 14.2, as cited in ND §1.2.
- **NH** = `gallai/05-technical-notes/near-half-mixed-vertices.pdf`.
- **Lean** = `lean/GallaiLean/NearDirac.lean`.
- Also `manuscripts/near-dirac/README.md` and `research/connections.md` §D.1, where they restate claims of ND.

**Independence.** I wrote everything in `research/audit/A17-scripts/` from the text of ND alone. No scripts accompany ND, so there is nothing non-independent to re-run.
- `a17_constants.py`: every numerical inequality in the proof, at the paper's constants and at worst cases of the free parameters.
- `a17_pipeline.py`: an end-to-end implementation of Steps 0–9 of §4. It uses real max-flow for Lemma 3.1 and real Hall matchings for Lemma 3.2. It checks every exactness claim and builds the two-apex graph J.
- `a17_apex.py`: the conversion in Lemma 4.2, from a Hamilton decomposition of J to D paths with prescribed ends.
- `a17_small_lemmas.py`: stress tests of Lemma 3.1, the identity of Lemma 4.1, and the profile construction of Lemma 5.1.

Outputs are in `A17-scripts/out/`.

Verdicts: **SOUND**; **GAP** (fixable; the fix is stated); **ERROR** (false; the false statement is identified); **UNCLEAR** (cannot be settled from the available material).

---

## 0. Summary table

| # | Item | Verdict | Note |
|---|---|---|---|
| N1 | **CKLOT Thm 1.3.5: quotation, numbering, definition of ε-bipartite** | **SOUND** | Verbatim against the v2 source (label `1factbip`). Section 1.3 numbers its environments 1.3.1 `bestposs`, 1.3.2 `lem:characteriseexpanders`, 1.3.3 `1factstrong`, 1.3.4 `undir_decomp`, 1.3.5 `1factbip`. The statement has no parity condition on n, no upper bound on D and no per-vertex condition. |
| N2 | **Application of CKLOT 1.3.5 (Lemma 4.2, Step 9)** | **SOUND** | (i) D = m − q is even, since q ≡ m (mod 2). (ii) J is simple: R ⊆ G, the apices are non-adjacent and each is joined to distinct vertices. (iii) J is D-regular: d_J(a_i) = \|Z₂\| + \|Z₁\|/2 = D and d_J(v) = d_R(v) + b′(v) = D. (iv) N = \|J\| = 2m + 2 + ρ and D ≥ (1/2 − ε_ex)(2m + 3) ≥ (1/2 − ε_ex)N. (v) A′ = A + a₁ has size m + 1 = ⌊N/2⌋ for ρ ∈ {0, 1}. (vi) e_J(A′) ≤ e_R(A) + D ≤ ε_ex N², and likewise for V(J) ∖ A′ = B + a₂. At ρ = 1, N = 2m + 3 is odd; the statement permits this. §1. |
| N3 | GGKO Thm 1.11 (and Thm 1.10(i)) quotation | SOUND | Verbatim; the numbering is confirmed. It is not used in any proof in ND. |
| N4 | SP quotations (Cor 14.24, Cor 14.26, Thm 14.27, Cor 14.39) | SOUND | Verbatim against pdftotext. ND §1.2's citations of SP 14.1, 14.2 and 14.5 are also correct. |
| N5 | **Constants: θ = min{ε_ex/2, 1/100}, c = θ/1000, q, D, m₀** | **SOUND**; two rounding nits | The order is consistent: ε_ex, then θ, then c, then m₀, with q and D depending on m. Every inequality holds simultaneously once q ≳ 158, i.e. m ≳ 158/θ. The binding one is p_v ≤ 0.51q in Step 0. Rounding nits: the cap ⌊q/100⌋ in (P4) and the slot capacity ⌊m/100⌋ in Step 3 make "102\|X\|" and "101cm" true only for large q and m, with enormous slack. Cor 1.2 needs m ≳ 2/c. §2. |
| N6 | **Lemma 3.1 (membership matrix, max-flow)** | **SOUND** | The cut capacity is α([r]∖R′) + e(R′, Y) + β(C′). The two "large" cases use the fact that ≥ 0.62r (resp. 0.62q) entries are allowed. The bound on forbidden entries, min(0.03q\|R′\|, 0.03r\|Y\|), is correct. The maximum of f on [0, 0.65]² is −0.01, at (0.65, 0); the only critical point (0.63, 0.60) is a saddle. Lean-verified (N35). 400 stressed instances, with forbidden sets at the limits and extreme margins: 0 failures. |
| N7 | **Lemma 3.2 (weaving, Hall)** | **SOUND** | Gaps have distinct left exits and right entries, and blocks have distinct entries and exits, so both degrees are ≥ k − 2M. Hall holds for k ≥ 4M (Lean). In (i), β_{k−1} exists since M < k − 1, and the Hall step runs on k − 1 ≥ 4M + 1. There are \|𝓑₁\| + \|𝓑₂\| − 1 joining edges. The path is simple because the blocks are disjoint. |
| N8 | **Lemma 4.1 (counting identity)** | **SOUND** | It is the handshake on each part. It holds for every integer ρ, not only ρ ∈ {0, 1}. Checked on 2,000 random (graph, partition, D). |
| N9 | **Lemma 4.2 (apex finish)** | **SOUND** | Pieces are non-empty because a₁a₂ ∉ E(J). A singular vertex v (a cycle contains a₁va₂) has b′(v) = 2 and is singular in exactly one cycle. A non-singular v has its apex edges in distinct cycles. A split at v changes only v's end count. The count is D − #singular + #singular = D. 1,824 synthetic conversions (§3.4), with up to 29 singular vertices, including all splits hosted in one cycle: all exact. |
| N10 | **Remark 4.3 and the abstract: "the balance condition is precisely what the [two-apex] finish requires"** | SOUND (computation); **GAP (wording)** | Equation (eq:forced) is correct. Necessity holds only (a) up to the error term and (b) for finishes in which the preliminary paths never use internal edges at X. Exactly: necessary is (c) with cm replaced by ≈ (1 ± ρ/2)q ± β₀, which is about 1000·cm; (c) uses cm. If the preliminary paths may use internal edges at X, the condition weakens by up to ~q\|X_S\|. §3.3. |
| N11 | Step 0 (visit numbers p_v ∈ [0.49q, 0.51q]) | SOUND | Every degree lies in [m − cm, m + 1 + cm]; p_v is integral because b ≡ d and D is even. |
| N12 | **Step 1 (kept internal edges, \|Λ\| ≤ 0.6q)** | **SOUND** | β′ is integral. Λ takes every integer value in [Λ₀ − e_H(B), Λ₀ + e_H(A)]. Both displayed bounds are correct, including the ρ(m − q)/2 bookkeeping. This is the only use of (c). |
| N13 | Step 2 (ends, slot types) | SOUND | At least (m − 2.5cm)/2 ≥ 0.45m ≥ 2q end candidates per shore. The position counts 2Λ⁺ + (q − \|Λ\|) = l_A and q − Λ = l_B are correct. Distinct end-sites. |
| N14 | Step 3 (internal matchings) | SOUND; nit | 101cm + 2cm + 2 < q. Nit: the capacity is ⌊m/100⌋. |
| N15 | **Step 4 (partner blocks u x u′, (P1)–(P4))** | **SOUND**; nit | The excluded total is ≈ 0.0302m + O(1), well below m/4 − cm. (P2) also forbids the same partner for x in two slots, so every spoke is used once. Nit: with cap ⌊q/100⌋, "102\|X\|" needs q ≫ 100; the true count is 2Σp_x/⌊q/100⌋ and the slack absorbs it. |
| N16 | Step 5 (forced memberships) | SOUND | Exclusive roles: Step 3 plus (P3). Row ≤ 1 + cm + q/100 ≤ 0.02q; column ≤ 2 + m/50 + 2cm ≤ 0.021m ≤ 0.03\|H_A\|. |
| N17 | **Step 6 (claim Σh^B_i = P_B; matrix margins)** | **SOUND** | The identity reduces exactly to the definition of Λ. Margins: rows in [0.47q, 0.51q], A-columns in [0.4\|H_A\|, 0.6\|H_A\|], B-columns in [0.47\|H_B\| − 0.021m, 0.53\|H_B\|]. The claim holds exactly in all 60 pipeline runs. |
| N18 | Step 7 (blocks; a_i − b_i = τ_i) | SOUND | The blocks are vertex-disjoint. An x-block on A has its middle vertex x ∈ B, which lies in no B-block. Checked in every slot of every run. |
| N19 | **Step 8 (weaving; M ≤ 1.03q; block numbers ≥ 4M + 2)** | **SOUND** | Cross edges between healthy vertices are used only as joining edges, ≤ 2 per visit. Spokes and F-edges are block edges of exactly one slot. min(a_i, b_i) ≥ 0.46m − O(cm) ≥ 0.45m ≥ 4.12q + 2. |
| N20 | **Step 9: every edge once, ends = b, all paths simple, count = m** | **SOUND** | The edges kept for R are R_A ∪ R_B, the internal edges at X, the edges inside X and the unused cross edges. d_R = D − b′ and e_R(S) = \|R_S\| + I_X(S) ≤ 1.77cm². The end count is l + b′ = b, and the number of paths is q + D = m. |
| N21 | **End-to-end simulation of Steps 0–9** | **No failure** (60/60) | m ∈ {240, …, 480}, ρ ∈ {0, 1} (30 runs each), up to 8 exceptional vertices with own(x)/m up to 0.74, Λ at both extremes ±0.6q, b(A) − b(B) between −8 and 6. Every exactness claim was asserted, and J was built and checked. §4. |
| N22 | Lemma 5.1 (standard profiles) | SOUND | e_A ≡ e_B (mod 2) at ρ = 0, and e is odd at ρ = 1. Values: b(A) − b(B) ∈ {0, ±2}, b(t) ≥ 1. Exhaustive over all roots on 4,000 random graphs. |
| N23 | **Corollary 1.2** | **SOUND** | γ = c²/20 gives \|X\| ≤ 0.85cm, mis ≤ 1 + γn + cm/2 ≤ cm, d(x) ∈ [(1 − c)m, (1 + c)m], cr(x) ≥ n/8 ≥ m/4, and \|e(A) − e(B) + ρm/2\| ≤ γn/2 ≤ cm, so (c) holds. Both parities and the rooted case at even n are covered. |
| N24 | Text after Cor 1.2 (D-regular case; "own up to about 3n/8") | SOUND; nit | ρ\|D − ⌊n/2⌋\| ≤ γn when \|D − n/2\| ≤ γn/2 and n ≥ 1/γ. **Nit: the PDF is stale.** It still says "n/4", which dff7439 changed to "3n/8" in the .tex; recompile. |
| N25 | **Corollary 1.3** | SOUND proof; **GAP (statement)** | The statement omits **\|X\| ≤ cm**, which is not part of (a) or (b) but is needed to apply Thm 1.1. Without it the claim is unproved (e.g. X = V can satisfy (a) and (b)). Fix: "any set X with \|X\| ≤ cm satisfying (a) and (b)". The README's "admissible" needs the same. |
| N26 | Remark 6.2 (maximum-cut exceptional set) | SOUND; GAP (wording) | The three bullets are correct (max cut ⇒ cr(x) ≥ d(x)/2). The last paragraph should say "a member G_n of a failure sequence, n large" rather than "a failure of Target D". |
| N27 | **ND §7.1(1): Thm 1.1 contains SP 14.27** | **SOUND** | With X = ∅ and ρ = 0, (c) is vacuous and (a) is SP's hypothesis. Take c_SP := c and m₀ := max(m₀, 2/c), so that \|b(A) − b(B)\| ≤ 2 ≤ cm. The rooted claim comes from Lemma 5.1(i). |
| N28 | ND §7.1(1)(a)–(d): the departures from SP's proof | SOUND | SP 14.27 has \|A\| = \|B\|. SP's odd-order case is one-apex (14.31). |
| N29 | **ND §7.1(2): the description of SP 14.31, 14.33, 14.37 and 14.38** | Non-containment SOUND; **GAP (wording)** | Both "not implied" directions are correct. The summary is inaccurate. 14.31 and 14.33 are *bipartite* with o(m) even-degree vertices and o(m) missing (14.33: shores m, m + 1 + r). 14.37 has 0 ≤ d ≤ cm, including d = 0 (= 14.27). 14.38 is a 2-colouring statement. "c ≤ 10⁻⁶" is not stated by SP for 14.37: its c is non-explicit, and 10⁻⁶ is 14.27's θ/1000. |
| N30 | ND §7.1(3): "returns the exceptional set of Cor 14.39 whenever the configuration is balanced" | GAP (wording) | Remark 6.2 uses its own threshold κ′ ≤ c/3, which may differ from SP's κ. It also needs three things: \|A\| = ⌊n/2⌋ exactly, exceptional degrees ≤ (1 + c)m, and (c). Say so. |
| N31 | ND §7.1(4): NH and Thm 1.1 are disjoint | SOUND | NH's mixed vertices have degree 2D ≈ n, which neither (a) nor (b) allows. |
| N32 | ND §1.4 (R2): "A vertex of degree (1/2 + β)n … must lie on almost every path" | **ERROR (wording; inconsequential)** | False as written. Such a vertex lies on ≥ (1/4 + β/2)n of ≤ n/2 paths, i.e. on a (1/2 + β)-fraction. Problem 7.2 states it correctly. |
| N33 | ND §7.2: "Two pieces of the solution are in place … What is missing is only the scheduling"; README "done"; connections §D.1 | **UNCLEAR (heuristic, overclaimed)** | Neither piece is proved. The one-apex window from Lemma 4.1 is \|2(e_R(A) − e_R(B)) + ρD\| ≤ D, which has width D and does not "disappear". The greedy contribution of a vertex x is up to d(x) ≤ (1 + c)m > D, and moving x changes the shore sizes. "Only the scheduling is missing" cannot be checked. §5.4. |
| N34 | Problem 7.2 and the closing paragraph of ND §7.2 | SOUND as heuristics | The counting is correct (visits ≥ d/2; one visit per path). "Only Problem 7.1 remains" correctly means "unbalanced": either \|A\| ≠ ⌊n/2⌋ or (c) fails. |
| N35 | **Lean `NearDirac.lean`** | **SOUND** | `lake build GallaiLean.NearDirac` succeeds (Lean v4.36.0, Mathlib v4.36.0, 2537 jobs). `#print axioms` gives [propext, Classical.choice, Quot.sound] for `matrix_cut_ineq`, `dense_bipartite_hall` and `cut_ineq_aux`, with no `sorry` or `native_decide`. The statements are exactly what the paper uses: f < 0 on [0, 13/20]², and Hall for \|L\| = \|R\| = k ≥ 4M with both degrees ≥ k − 2M, applied with k − 1 in case (i). The reduction from Lemma 3.1 to f, and the rest of Lemma 3.2, are not formalised; ND §8 says so. |
| N36 | `CITATIONS.md` | **GAP (documentation)** | It says §2 of the .tex reproduces SP 14.24, 14.26, 14.27, 14.33, 14.35, 14.37, 14.38, 14.39 and 14.40. §2 reproduces only 14.24, 14.26, 14.27 and 14.39. 14.38's κ is used but not quoted. |
| N37 | Bibliography | nit | [DEC] is never referred to. [SP] and [NH] are referred to by name but never `\cite`d. |

**Overall.** **Theorem 1.1 is correct.** Every step of §4 is SOUND, and so are the four lemmas it uses (3.1, 3.2, 4.1, 4.2). I checked each requirement I was asked to check:
- the hypotheses of CKLOT Theorem 1.3.5 hold exactly for J, at both parities;
- the constants are consistent;
- every edge is used exactly once;
- the path ends match b exactly;
- all paths are simple;
- the count is exactly q + D = m.

An independent end-to-end implementation of Steps 0–9 confirms the bookkeeping on 60 instances, with ρ ∈ {0, 1} and exceptional vertices of own-shore degree up to 0.74m. **Corollary 1.2 is correct** at both parities, including the private-leaf bound at even order. **Corollary 1.3 is correct once "\|X\| ≤ cm" is added to its statement** (N25). Lean builds with the standard axioms and states what the paper uses.

The remaining items are wording and documentation:
- the "precisely necessary" claim (N10);
- the summary of SP 14.31–14.38 (N29);
- "returns the exceptional set of Cor 14.39" (N30);
- one false informal sentence in (R2) (N32);
- the "pieces in place" of ND §7.2, which are heuristics rather than results (N33);
- `CITATIONS.md` (N36);
- a stale PDF (N24).

**No mathematical error affects any theorem, lemma or corollary.**

**Current status (ebfcdd8, §9).** The revision fixes N10 (in the manuscript), N24, N25, N26, N29, N30, N32 and N36. Corollary 1.3 is now **SOUND** as stated. The new material is correct: the quotes of CKLOT 1.3.4 and SP 14.37/14.38, the credits to SP 14.30 and SP §14.18, the "θm/20" remark, and the rewritten proofs of Cor 1.2 and Cor 1.3. Still open:
- N33: ND §7.2 still presents its two heuristics as "pieces of the solution … in place", and the README still says they are "done";
- N10, residual: connections §D.1 still says "This is why … need SP's one-apex removal scheme";
- nits N15 (the ⌊q/100⌋ cap in (P4)) and N37 ([DEC] is still never referred to).

None of these affects a result.

---

## 1. External theorems

### 1.1 CKLOT Theorem 1.3.5

From `1factrevision.tex` (arXiv:1401.4159v2), lines 591–593 and 664–671:

> We say that G is ε-bipartite if there exists A ⊆ V(G) with |A| = ⌊n/2⌋ such that e(A), e(V(G)∖A) ≤ εn². …
> **Theorem** (`1factbip`). There are ε_ex > 0 and n₀ ∈ ℕ such that the following holds. Let n ≥ n₀ and suppose that D ≥ (1/2 − ε_ex)n is even. Suppose that G is a D-regular graph on n vertices which is ε_ex-bipartite. Then G has a Hamilton decomposition.

**Numbering.** The counter is `firstthm`, numbered within section. Section 1.3 ("Derivation of Theorems … from the Main Structural Results") contains, in order:
- 1.3.1 Prop `bestposs`;
- 1.3.2 Lemma `lem:characteriseexpanders`;
- 1.3.3 Thm `1factstrong`;
- 1.3.4 Thm `undir_decomp`;
- 1.3.5 Thm `1factbip`.

So "Theorem 1.3.5" is right, and CITATIONS.md's remark that 1.3.4 is not used is right.

**What the statement does not require.** The ND quote is verbatim. The statement has:
- no parity condition on n;
- no upper bound on D;
- no connectivity or per-vertex condition.

### 1.2 Each hypothesis, as applied to J (Lemma 4.2, Step 9)

| Hypothesis | Where checked | Verdict |
|---|---|---|
| D even | q is the least integer ≥ θm with q ≡ m (mod 2), so D = m − q ≡ 0 | ✓ |
| J simple | R ⊆ G is simple; a₁, a₂ are new, non-adjacent and joined to sets | ✓ |
| J D-regular | 2\|Z₂\| + \|Z₁\| = b′(V) = 2D, so \|Z₁\| is even and d(a_i) = \|Z₂\| + \|Z₁\|/2 = D. Old vertices: d_R + b′ = D | ✓ |
| D ≥ (1/2 − ε_ex)N | N = 2m + 2 + ρ ≤ 2m + 3. D ≥ m − θm − 2 ≥ m + 3/2 − ε_ex(2m + 3) ⟺ (2ε_ex − θ)m ≥ 7/2 − 3ε_ex, true for large m since θ ≤ ε_ex/2 | ✓ |
| A part of size ⌊N/2⌋ | \|A + a₁\| = m + 1 = ⌊(2m + 2 + ρ)/2⌋ for ρ ∈ {0, 1} | ✓ |
| ε_ex-bipartite | e_J(A′) = e_R(A) + \|N(a₁) ∩ A\| ≤ e_R(A) + D, and likewise for B + a₂. With e_R(S) ≤ 1.77cm² ≤ 0.0009·ε_ex·m², this is ≤ ε_ex N² | ✓ |
| N ≥ n₀ | m ≥ m₁ | ✓ |

**Odd order.** At ρ = 1 the graph J has odd order 2m + 3, and D-regularity at odd order is consistent with D even. This is the first use of 1.3.5 at odd N in the archive's two-apex scheme. SP 14.27, 14.31 and 14.33 all use N = 2m + 2; NH also uses odd N. The statement permits odd N. A consistency check: in a D-regular J with parts m + 1 and m + 2, Lemma 4.1 forces e_J(B′) − e_J(A′) = D/2, and the hypothesis e_R(B) + D ≤ ε_ex N² allows it.

(SP 14.27's paraphrase of 1.3.5, "sizes strictly between N/2 − 1 and N/2 + 1", is SP's own wording. ND uses the exact definition, so the paraphrase is irrelevant here.)

### 1.3 GGKO and SP

- **GGKO.** `Introduction.tex` has Theorem `thm:n/2` (1.10) and Theorem `thm:Delta/2` (1.11). The numbering counts Thm 1.1, Conj 1.2–1.4, Thms 1.5–1.7, Conj 1.8, Thm 1.9. The quote of 1.11 and the definition of weak quasirandomness are verbatim. ND's proofs do not use GGKO, as ND says.
- **SP.** The four quoted statements match pdftotext word for word: 14.24 on p. 158, 14.26 and 14.27 on p. 162, 14.39 on p. 171. SP Thm 14.1 (exact profiles at δ ≥ (1/2 + ε)n), Cor 14.2 and Thm 14.5 (the odd-order floor iff ≥ k missing edges) are as ND §1.2 describes.

---

## 2. Constants (`a17_constants.py`)

The paper's choices are θ = min{ε_ex/2, 1/100}, c = θ/1000, q = the least integer ≥ θm with q ≡ m, and D = m − q. The script evaluates each inequality at its worst case over:
- degrees in [m − cm, m + 1 + cm];
- \|X\| ≤ cm;
- b ∈ {0, 1, 2} and \|b(A) − b(B)\| ≤ cm;
- ρ ∈ {0, 1}.

Integer parts are taken honestly (⌊m/100⌋, ⌊q/100⌋). The script then finds the least m₀ from which all of them hold:

| ε_ex | θ | c | m₀ (Thm 1.1) | binding inequality | m₀ (Cor 1.2) |
|---|---|---|---|---|---|
| 10⁻² | 5·10⁻³ | 5·10⁻⁶ | ≈ 3.1·10⁴ (q = 158) | p_v ≤ 0.51q (Step 0) | ≈ 4.0·10⁵ (2 ≤ cm) |
| 10⁻³ | 5·10⁻⁴ | 5·10⁻⁷ | ≈ 3.1·10⁵ | same | ≈ 4.0·10⁶ |
| 10⁻⁴ | 5·10⁻⁵ | 5·10⁻⁸ | ≈ 3.1·10⁶ | same | ≈ 4.0·10⁷ |
| 10⁻⁶ | 5·10⁻⁷ | 5·10⁻¹⁰ | ≈ 3.1·10⁸ | same | ≈ 4.0·10⁹ |

All the "small enough" requirements are achievable simultaneously. Each one is a statement "q ≥ const" or "m ≥ const/ε_ex", and none involves a circular choice.

- **Cor 1.2** additionally needs cm/2 ≥ 1 + γn, i.e. m ≳ 2.2/c. That is covered by "n₀ = 2m₀ + 2 large".
- **Remark 6.2** uses κ′ ≤ c/3, chosen after c.

**Rounding nits (no effect on validity).**
- *Step 3.* The slot capacity "m/100" must be ⌊m/100⌋. The count of full slots is then ≤ 1.01cm²/⌊m/100⌋, which tends to 101cm.
- *Step 4.* The cap "q/100" must be ⌊q/100⌋, which is ≥ 1 only for q ≥ 100. With ⌊q/100⌋ = 1 (q < 200), the number of capped vertices is ≤ 1.02q\|X\|, not "102\|X\|". The total exclusion stays ≈ 0.03m ≪ m/4 − cm, so the claim holds, but the intermediate figure needs "for large q" or the floor.

---

## 3. The lemmas

### 3.1 Lemma 3.1 (membership matrix)

- **The cut.** A cut is a set R′ of rows and a set C′ of columns on the source side. Its capacity is α([r]∖R′) + e(R′, Y) + β(C′), where Y = [q]∖C′. Edges from rows outside R′ to C′ run backwards and are not counted. The condition is (eq:cutcond).
- **The large cases.** If \|R′\| ≥ 0.65r, every column has ≥ 0.62r allowed entries in R′, which is ≥ β_j. The case \|Y\| ≥ 0.65q is symmetric.
- **The generic case.** The forbidden entries in R′ × Y number at most min(0.03q\|R′\|, 0.03r\|Y\|). With x, y < 0.65 it suffices that f(x, y) ≤ 0.
  - **Maximum of f.** By symmetry take y ≤ x. Then g = 0.6x + 0.63y − 0.4 − xy has gradient zero only at (0.63, 0.60), which lies inside the triangle and is a saddle (Hessian [[0, −1], [−1, 0]]). On the boundary the maximum is −1/100, at (0.65, 0). The other two edges give −0.023 at (0.65, 0.65) and −0.021775 at x = y = 0.615.
  - The script confirms this exactly with rationals, and on a 1301² grid.
- **Integrality.** Max-flow integrality gives the 0/1 matrix.
- **Stress test** (`a17_small_lemmas.py`, 400 instances):
  - r ∈ {40, …, 150}, q ∈ {34, …, 100};
  - forbidden sets at the exact limits: a dense block R₀ × C₀ with \|R₀\| = ⌊0.03r⌋ and \|C₀\| = ⌊0.03q⌋, a diagonal band, or random;
  - margins at the extremes (all-top or all-bottom), with the largest margins put on the rows and columns of the block.

  Max-flow saturated in every case.

**SOUND.**

### 3.2 Lemma 3.2 (weaving)

- **Part (ii).** Write the gaps as g_j = (β_{j−1}, β_j). The k left exits are distinct, and so are the k right entries, because the blocks are distinct and vertex-disjoint. Distinct blocks of 𝓑₂ have distinct entries and distinct exits. So each gap accepts ≥ k − 2M blocks, and each block lies in ≥ k − 2M gaps.
- **Hall.**
  - For \|S\| ≤ k − 2M, a single member of S suffices.
  - For \|S\| > k − 2M ≥ 2M, every block has a neighbour in S.

  This needs k ≥ 4M, which (ii) gives as k ≥ 4M + 1. Lean verifies this step (N35).
- **Part (i).** s₂ is non-adjacent to ≤ M of the k − 1 exits other than s₁'s, so β_{k−1} exists since M < k − 1. The Hall step then runs on k − 1 gaps and blocks, with degrees ≥ k − 1 − 2M and k − 1 ≥ 4M + 1.
- **Edge count.** There are 2(k − 1) + 1 = \|𝓑₁\| + \|𝓑₂\| − 1 joining edges in (i), and 2k in (ii).
- **Blocks.** Interior vertices of a block are arbitrary, so the x-block u x u′ on A, with x ∈ B, is admissible.

**SOUND.**

### 3.3 Lemma 4.1 and Remark 4.3

**The identity.** It is two handshakes subtracted. It holds for every integer ρ; tested on 2,000 random instances.

**Remark 4.3.** (eq:forced) and \|l(A) − l(B)\| ≤ 2q are correct. The abstract says the identity "shows that the balance condition is precisely what the Hamilton-decomposition finish of SP 14.27 requires". The README says "necessary for this two-apex architecture". connections §D.1 says "this is why imbalanced configurations … need SP's one-apex removal scheme". What the identity actually gives:

- **Necessity, with X-internal edges kept.** Suppose the preliminary paths never use internal edges at X, so that I_X(S) ≤ e_R(S) ≤ e(S). Write β₀ = (b(A) − b(B))/2. Then
  - I_X(A) + ρm/2 ≤ e(B) + (1 + ρ/2)q − β₀, and
  - I_X(B) ≤ e(A) + ρm/2 + (1 − ρ/2)q + β₀.

  This is (c) with cm (= θm/1000) replaced by ≈ q (= θm): about 1000 times weaker.
- **Without that restriction.** If the preliminary paths may use internal edges at X (as SP 14.30 does with labelled pairs), each x ∈ X_S can shed up to 2p_x ≈ q of them. The necessary condition then weakens by up to ≈ q\|X_S\|, which can be ≫ q.
- **What the proof needs.** The proof uses (c) only in Step 1, and Step 1 has slack of order q. Concretely: replace cm by θm/4 in both inequalities of (c), and 0.6q by 0.76q in Step 1. Step 2 still has l_A, l_B ∈ [0.24q, 1.76q] ⊆ [0, 0.45m], and no later step uses the bound on Λ. So Theorem 1.1 holds with (c) weakened to "+θm/4". The sufficient and necessary conditions for this architecture then agree up to a constant factor in the error term.

**Verdict.** The computation is SOUND. "Precisely" is a GAP (wording). Proposed fix: §7, F2. The strengthening is optional.

### 3.4 Lemma 4.2 (apex finish)

The proof is as summarised in N9. Two points need care, and both hold.
- **The singular vertex.** A singular v uses both apex edges in C_{j(v)}. It therefore has no apex edge in any other cycle, so it is interior to its piece in C_{j′}.
- **Splits sharing a host.** When several singular vertices choose the same host cycle, an earlier split leaves every other vertex of the piece interior to one of its halves.

`a17_apex.py`:
- **Construction.** J is the union of D/2 cycles of a Walecki decomposition of K_N under a random relabelling, omitting the cycle that contains a₁a₂. So J is a genuine Hamilton-decomposed, D-regular, simple graph with a₁a₂ ∉ E(J).
- **Runs.** N odd in 9–61 and every even D from 4 to N − 3: 1,824 conversions. 1,400 of them have ≥ 1 singular vertex, up to 29, and half put every split on one host cycle.
- **Result.** Every run gives exactly D paths with b′(v) ends at every v, and the paths partition E(R) exactly.

**SOUND.**

---

## 4. The proof of Theorem 1.1, step by step, and the end-to-end check

**The argument.** The step-by-step verdicts are in rows N11–N20 of the table. The exactness requirements I was asked to check:

- **Every edge exactly once.**
  - F-edges are each assigned to exactly one slot and become block edges there.
  - Spokes xu are distinct across slots by (P2), and spokes of different x are different edges.
  - Joining edges are unused cross edges between healthy vertices at the moment of use.
  - These three classes are pairwise disjoint: internal–healthy, X–healthy cross, and healthy–healthy cross.
  - The residual R is the rest of the graph: R_A ∪ R_B, the internal edges at X, the edges between exceptional vertices, and the unused cross edges.
  - Lemma 4.2 partitions E(R).
- **Ends match b.**
  - In the preliminary phase, v is an end exactly l_v times; X is never an end; l ≤ b.
  - In the Hamilton phase, v is an end b′(v) = b(v) − l_v times.
- **Simplicity.** P_i is simple by Lemma 3.2, since its blocks are vertex-disjoint (Step 7). The Hamilton-phase paths are sub-paths of Hamilton cycles.
- **Count.** q + D = m.

**End-to-end implementation** (`a17_pipeline.py`, 60 instances, `out/pipeline.txt`). The paper's constants need m ≳ 3·10⁴ even for ε_ex = 10⁻² (§2), so the construction is run at m ∈ {240, 320, 400, 480} with q ≈ 0.04–0.06m. The numerical sufficient conditions of Lemma 3.1 do not hold at this size: the row-forbidden bound 0.03q is < 1. So real max-flows replace them. Lemma 3.2's hypothesis k ≥ 4M + 2 *did* hold in every slot of every run.

Instances:
- complete bipartite, minus up to 4 random cross matchings;
- healthy internal matchings, so own(v) ≤ 2 + \|X\|;
- 0–8 exceptional vertices with own(x) ∈ [0.05m, 0.74m], cross degree ≥ 0.26m, d(x) = m ± 2;
- made Step-1-solvable by adding healthy internal edges on the light side, as (c) requires;
- ρ = 0 and ρ = 1 equally often;
- Λ chosen randomly, or at the two extremes ±0.6q;
- b(A) − b(B) between −8 and 6 (realised values).

The Step 3 capacity was relaxed when the small m needed it. In the paper's regime \|F\| ≤ 1.01cm² is about 1/100 of the total capacity q·m/100.

**Asserted in every instance:**
- Step 6's claim Σh^B_i = P_B holds exactly;
- a_i − b_i = τ_i in every slot;
- the blocks are vertex-disjoint;
- each P_i is a simple path of G joining the two prescribed end-sites;
- the paths are pairwise edge-disjoint and avoid R_A ∪ R_B and every internal edge at X;
- every F-edge is used;
- every v lies on exactly p_v paths and is an end of exactly l_v; X is never an end;
- d_R(v) = D − b′(v), b′ ∈ {0, 1, 2}, b′(V) = 2D;
- e_R(S) = \|R_S\| + I_X(S);
- Lemma 4.1 holds on R;
- J is simple and D-regular, \|A + a₁\| = ⌊N/2⌋, and e_J(A′) ≤ e_R(A) + D, e_J(B′) ≤ e_R(B) + D;
- q + D = m.

**Result: 60/60 pass.**

---

## 5. Corollaries, remarks, and the relation to SP

### 5.1 Lemma 5.1 and Corollary 1.2

**Lemma 5.1.**
- *ρ = 0.* The degree sums of A and B differ by 2(e(A) − e(B)), so the numbers of odd vertices agree mod 2, and \|A\| = \|B\| gives e_A ≡ e_B.
  - If e_A and e_B are both even, b(A) = b(B) = m.
  - If both are odd, b(S) = m + 1 and b(S′) = m − 1. When t is even, it can be doubled, because then e_S ≥ 1.
- *ρ = 1.* The number of even vertices is e = n − #odd, which is odd. The two cases give b(A) − b(B) = 0 and −2.

Exhaustive over all roots on 4,000 random graphs with 1 ≤ m ≤ 10.

**Corollary 1.2.**
- **Bounds.** \|X\| ≤ 4γn²/(cm) ≤ 17γm/c = 0.85cm, using n² ≤ 4.25m² for m ≥ 17. For v ∉ X, mis(v) ≤ (m + 1) − δ + own(v) ≤ 1 + γn + cm/2 ≤ cm. For x ∈ X, d(x) ∈ [(1 − c)m, (1 + c)m] and cr(x) ≥ n/8 ≥ m/4.
- **Balance.** Σ_A(d − m) − Σ_B(d − m) = 2(e(A) − e(B)) + ρm, so \|e(A) − e(B) + ρm/2\| ≤ γn/2 ≤ cm, and I_X(S) ≤ e(S) gives (c).
- **Conclusion.** With the profile of Lemma 5.1 (\|b(A) − b(B)\| ≤ 2 ≤ cm), Theorem 1.1 gives m = ⌊n/2⌋ paths at both parities. At even n, b(t) ≥ 1, so a path ends at t and the pendant edge extends it: p(G^t) ≤ n/2.

The floor at odd order and the private-leaf bound at even order are correctly separated. No private-leaf claim is made at odd order, and Target D asks for none. **SOUND.**

The sentence about D-regular graphs is correct: the left-hand side is ρ\|D − m\|, and \|D − m\| ≤ \|D − n/2\| + 1/2 ≤ γn when n ≥ 1/γ. A consistency check: a D-regular graph on shores (m, m + 1) has e(B) − e(A) = D/2, which is exactly what (c) asks at ρ = 1.

### 5.2 Corollary 1.3 and Remark 6.2

**Corollary 1.3.**
- **The logic is right.** At even n the failure must be at a private-leaf root t, so the rooted profile at t applies. At odd n it is the floor. Both contradict Theorem 1.1.
- **GAP (N25).** The statement quantifies over "any set X satisfying hypotheses (a) and (b)". Theorem 1.1 also needs \|X\| ≤ cm, which is a separate hypothesis in its statement. For instance X = V(G_n) satisfies (a) vacuously, and (b) whenever every degree is (1 ± c)m with cr ≥ m/4. For that X, (c) reads \|e(A) − e(B) + ρm/2\| ≲ cm, and nothing in ND proves that this fails.
- **Fix.** Add "with \|X\| ≤ cm" (§7, F1).

**Remark 6.2.**
- **SOUND bullets.**
  - Σ own = o(n²) and \|A\|, \|B\| = n/2 + o(n), as in SP 14.39's proof.
  - mis(v) ≤ max(\|A\|, \|B\|) − δ + own(v) ≤ o(n) + cn/3 < cm.
  - Maximality of the cut gives cr(x) ≥ d(x)/2 ≥ n/4 − o(n) ≥ m/4.
  - The extra conditions are correctly listed: an exactly balanced cut, and exceptional degrees ≤ (1 + c)m. Also d(x) ≥ δ ≥ (1 − c)m and \|X\| = o(n) ≤ cm.
- **GAP (wording).** The last paragraph speaks of "a failure of Target D". It should be "a member G_n of a failure sequence, for n large", since Corollary 1.3 is asymptotic.

### 5.3 Relation to SP §14 (ND §7.1)

- **(1) Theorem 1.1 contains SP 14.27: SOUND.** Set X = ∅ and ρ = 0. Then (c) reads 0 ≤ e(B) + cm and 0 ≤ e(A) + cm, which is vacuous, and (a) is SP's hypothesis verbatim.

  As an existence statement, SP 14.27 follows with c_SP := c and m₀ := max(m₀, ⌈2/c⌉). The rooted part follows from Lemma 5.1(i), which is SP's own profile argument (SP p. 164).

  Departures (a)–(d) are accurately described. SP 14.27 requires \|A\| = \|B\|. SP handles odd order near K_{m,m+1} by the one-apex Theorem 14.31; SP p. 165 records the same two-auxiliary-vertex obstruction \|t(A) − t(B) − D(a − b)\| ≤ 2q.
- **(2) SP 14.31, 14.33, 14.37, 14.38.** The non-containment claims are SOUND:
  - Theorem 1.1 cannot give d ≥ 2.
  - At d = 1 it needs e(B) ≳ m/2, which a graph near K_{m,m+1} need not have.
  - Conversely, own(x) up to 3m/4 on a linear X is outside every SP hypothesis, in every bipartition: moving x across leaves own(x) ≥ min(d_A(x), d_B(x)).
  - The generalisation of Remark 4.3 to \|B\| = m + d, "keep about dD/2 more internal edges", is correct for nearly balanced profiles. Lemma 4.1 holds for any integer ρ and does not depend on where the apices are placed.

  The description is inaccurate (**GAP, wording**). What SP actually proves:
  - **14.31:** bipartite, shores m and m + 1, along a family with h = o(m) missing and o(m) even-degree vertices;
  - **14.33:** bipartite, shores m and m + 1 + r, with e + h + r = o(m);
  - **14.37:** internal edges allowed, shores m and m + d with **0** ≤ d ≤ cm, and d = 0 is 14.27;
  - **14.38:** a two-colouring statement with own ≤ κn, where κ = min{c/40, 1/100}.

  Also, "SP 14.37 requires … c ≤ 10⁻⁶": SP's proof of 14.37 is by compactness and its c is not explicit. The figure 10⁻⁶ is SP 14.27's θ/1000 with θ ≤ 10⁻³.
- **(3) Cor 14.39.** The claim is SOUND in substance and imprecise in wording (GAP). The X of Remark 6.2 has threshold κ′ ≤ c/3, not SP's κ = min{c₁₄.₃₇/40, 1/100}, and the two may differ. "Whenever the configuration is balanced" must spell out all three conditions: \|A\| = ⌊n/2⌋, Δ(X) ≤ (1 + c)m, and (c).
- **(4) NH: SOUND.** NH's mixed vertices have degree 2D ≈ n. Such a vertex cannot be healthy, whose degree is ≤ m + 1 + cm, and cannot be in X, whose degree is ≤ (1 + c)m.

### 5.4 ND §1.4 and §7.2 (what remains)

- **(R2), first sentence: ERROR (wording).** "A vertex of degree (1/2 + β)n with fixed β > 0 must lie on almost every path" is false for small β. It must lie on ≥ ⌈d/2⌉ ≥ (1/4 + β/2)n of the ≤ n/2 paths: a (1/2 + β)-fraction, not almost all. Problem 7.2 has the correct count. The rest of (R2) is correct:
  - in a two-apex finish each vertex lies on exactly one piece of each Hamilton cycle, so on D/2 pieces plus ≤ q preliminary paths;
  - such a vertex therefore needs ≥ (βn − O(q))/2 extra visits;
  - NH handles this by splitting.
- **ND §7.2, "Two pieces of the solution are in place": UNCLEAR.** Neither piece is proved, and both are imprecise.
  - *The one-apex window.* With one apex, b′ ∈ {0, 1} and b′(V) = D. Lemma 4.1 then requires \|2(e_R(A) − e_R(B)) + ρD\| ≤ D: a window of width D on e_R(A) − e_R(B). The obstruction is relaxed from width ≈ 2q to width D; it does not "disappear". With linear X, I_X(A) − I_X(B) can be ≈ \|X\|·m ≫ D.
  - *The greedy side-choice.* Moving x between shores changes e(A) − e(B) by up to d(x) ≤ (1 + c)m, which exceeds D. Moving vertices also unbalances the shore sizes, which is (R1) again, and the interaction of edges inside X is not addressed. The quoted bound "within ±D" is therefore not justified.
  - *"What is missing is only the scheduling of the two-sided pairs."* This cannot be checked.
  - The README ("The one-apex identity and the greedy side-choice are done") and connections §D.1 ("This is why … need SP's one-apex removal scheme") repeat these claims as results. They should be labelled heuristic (§7, F6).
- **Problem 7.2 and the final paragraph: SOUND as heuristics.** By SP 14.26, max{Δ, odd} = n − o(n). Read through Remark 6.2, "only Problem 7.1 remains, and only in the unbalanced case" is accurate, where "unbalanced" means \|A\| ≠ ⌊n/2⌋ or (c) failing.

---

## 6. Lean (`lean/GallaiLean/NearDirac.lean`)

```
export PATH=$HOME/.elan/bin:$PATH; cd lean; lake exe cache get; lake build GallaiLean.NearDirac
  → Build completed successfully (2537 jobs).   [only "module system" import warnings]
#print axioms NearDirac.matrix_cut_ineq      → [propext, Classical.choice, Quot.sound]
#print axioms NearDirac.dense_bipartite_hall → [propext, Classical.choice, Quot.sound]
#print axioms NearDirac.cut_ineq_aux         → [propext, Classical.choice, Quot.sound]
```

The file contains no `sorry`, `admit`, `axiom` or `native_decide`, and `GallaiLean.lean` imports it (line 58).

**The statements match the uses.**
- **`matrix_cut_ineq`.** ∀ x y : ℝ with 0 ≤ x ≤ 13/20 and 0 ≤ y ≤ 13/20, 3/5·x + 3/5·y − 2/5 − x·y + 3/100·min x y < 0. This is exactly f < 0 on [0, 0.65]². The proof splits at x ≤ 0.63 and uses the nlinarith hints (x − y)(0.63 − x) ≥ 0, y(x − 0.63) ≥ 0 and (x − 0.615)² ≥ 0, which matches the paper's boundary analysis.
- **`dense_bipartite_hall`.** Finite types with card L = card R = k, 4M ≤ k, every l related to ≥ k − 2M elements and every ρ to ≥ k − 2M. The subtraction is in ℕ but is not truncated, because 4M ≤ k. The conclusion is an injective f : L → R inside the relation, which is a perfect matching since \|L\| = \|R\|. It is derived from Mathlib's `Finset.all_card_le_biUnion_card_iff_exists_injective`. It is applied with k in (ii), where k ≥ 4M + 1, and with k − 1 in (i), where k − 1 ≥ 4M + 1.

**Not formalised, as ND §8 says:**
- the reduction of Lemma 3.1's cut condition to f;
- the construction of the path from the matching;
- everything asymptotic.

**SOUND.**

---

## 7. Proposed fixes (not applied; the manuscript is not edited)

- **F1 (N25, Cor 1.3).** "…and any set X **with \|X\| ≤ cm** satisfying hypotheses (a) and (b) of Theorem 1.1…". The README's "every admissible partition and exceptional set" should define admissible as \|A\| = ⌊n/2⌋, \|X\| ≤ cm, (a) and (b).
- **F2 (N10, abstract and Remark 4.3).** Replace "shows that the balance condition is precisely what the Hamilton-decomposition finish of SP 14.27 requires" by:

  > shows that, for a two-apex Hamilton finish after q preliminary paths that keeps the internal edges at X for the Hamilton phase, a condition of the same form as the balance condition—with error term of order q instead of cm—is necessary

  Optionally strengthen Theorem 1.1 by replacing cm with θm/4 in (c) (§3.3). connections §D.1: "This is why…" should become "This is the obstruction for the two-apex scheme with X-internal edges kept".
- **F3 (N29, ND §7.1(2)).** Replace the first sentence by:

  > SP Theorems 14.31 and 14.33 treat bipartite graphs on shores m, m+1 (resp. m, m+1+r) with o(m) missing neighbours and o(m) even-degree vertices; Theorem 14.37 allows o(m) internal degree on shores m, m+d with 0 ≤ d ≤ cm (d=0 being 14.27), and Corollary 14.38 is its two-colouring form; none allows an exceptional set.

  Replace "with c ≤ 10⁻⁶" by "(SP's constant is not explicit; at d = 0 it is at most that of 14.27, θ/1000 ≤ 10⁻⁶)".
- **F4 (N30, ND §7.1(3)).** Replace the item by:

  > Theorem 1.1 proves the floor and rooted bounds for G itself (with the exceptional set of Remark 6.2, of threshold κ′ ≤ c/3) whenever the maximum cut has |A| = ⌊n/2⌋, the exceptional degrees are at most (1+c)m, and the balance condition holds.
- **F5 (N32, (R2)).** Replace "must lie on almost every path" by "must lie on at least (1/4 + β/2)n of the at most n/2 paths".
- **F6 (N33, ND §7.2, README, connections §D.1).**
  - "Two pieces of the solution are in place" → "Two heuristic observations".
  - State the one-apex window as \|2(e_R(A) − e_R(B)) + ρD\| ≤ D.
  - Either justify "within ±D" or weaken it to "within ± max_x d(x)".
  - Delete "What is missing is only the scheduling of the two-sided pairs".
  - README "done" → "sketched".
- **F7 (N26, Remark 6.2).** "take a failure of Target D" → "take a member G_n, n large, of a failure sequence".
- **F8 (N36, CITATIONS.md).** "The full statements of Cor 14.24, Cor 14.26, Thm 14.27 and Cor 14.39 are reproduced in §2 of near-dirac.tex". Either add 14.38, whose κ §2 uses, or drop the claim about 14.33–14.40.
- **F9 (N24).** Recompile `near-dirac.pdf`: it predates dff7439 and still reads "n/4".
- **F10 (N5, N14, N15, N37).** Write ⌊m/100⌋ and ⌊q/100⌋, and "at most 1.02q\|X\|/⌊q/100⌋ ≤ 103.1\|X\| for q ≥ 10⁴". Alternatively keep q/100 and require q ≥ 10⁴. Remove the unused [DEC] or cite it.

---

## 8. Scripts

| Script | What it checks | Output |
|---|---|---|
| `a17_constants.py` | Every inequality of §4 and Cor 1.2 at the paper's constants (worst cases; honest floors); least m₀ per ε_ex; exact maximum of f in Lemma 3.1 | `out/constants.txt` |
| `a17_pipeline.py [n]` | End-to-end Steps 0–9 with real max-flow and Hall matchings; all exactness assertions; J | `out/pipeline.txt` (60/60) |
| `a17_apex.py` | Lemma 4.2's conversion on 1,824 Hamilton-decomposed synthetic J (Walecki) | `out/apex.txt` |
| `a17_small_lemmas.py` | Lemma 3.1 stress (400), Lemma 4.1 identity (2,000), Lemma 5.1 profiles (4,000 graphs, all roots) | `out/small_lemmas.txt` |

They need Python 3 and networkx. The Lean check uses only the commands in §6.

---

## 9. Re-audit of the revision ebfcdd8 (current text; merged into `claude/audit-a17` at f01bd3b)

**What changed.** `git diff 981c46d f01bd3b -- manuscripts/near-dirac`:
- `near-dirac.tex`: +41/−23 lines, in ebfcdd8 and 43dcd85;
- `README.md` and `CITATIONS.md`;
- a recompiled `near-dirac.pdf` (16 pp, created 03:52:25 UTC, 10 s before the ebfcdd8 commit; its text matches the .tex);
- a new `near-dirac.toc`.

`lean/GallaiLean/NearDirac.lean` and the Lean toolchain files are unchanged. I rebuilt at f01bd3b: `lake build GallaiLean.NearDirac` succeeds, and `#print axioms` gives the same three standard axioms for all three theorems.

The proof of Theorem 1.1 changed in only two places: a sentence added to Step 1 and the figures in Step 3 (both checked below). The construction is the same, so the scripts of §8 still apply unchanged.

### 9.1 Status of the first-pass findings

| # | First pass (981c46d) | Change in ebfcdd8 | Status |
|---|---|---|---|
| N25 | Cor 1.3 omits \|X\| ≤ cm (GAP) | The statement now reads "any set X **with \|X\| ≤ cm** satisfying (a) and (b)". The proof is now direct: for ⌊n/2⌋ ≥ m₀, (c) together with Theorem 1.1 and Lemma 5.1 contradicts the defining failure. The README says "with \|X\| ≤ cm". | **FIXED — Cor 1.3 SOUND** |
| N10 | "precisely what the finish requires" (GAP, wording) | The abstract now says the identity, "whose bipartite case is SP's counting obstruction (SP §14.18), explains why some balance condition of this kind is needed". Remark 4.3 adds: "sufficient, not necessary … the slack cm in (c) could be raised to about θm/20 … relies on the choice to keep every internal edge at X". **θm/20 checked:** Λ₀ − e_H(B) ≤ θm/20 + cm/2 − ρq/2 ≤ 0.051q, and Λ₀ + e_H(A) ≥ −θm/20 − cm/2 − ρq/2 ≥ −0.551q, so \|Λ\| ≤ 0.6q is still attainable. The README now says "the counting identity behind the balance condition". | **FIXED in ND and README.** Residual: connections §D.1, line 136, still says "This is why imbalanced configurations … need SP's one-apex removal scheme" (doc only). |
| N29 | Summary of SP 14.31, 14.33, 14.37, 14.38 inaccurate; "c ≤ 10⁻⁶" (GAP) | Rewritten as three bullets. 14.31 and 14.33: bipartite, shores m and m + 1 + r, with r, the missing degree and the number of even-degree vertices all o(m) (14.31 is r = 0). 14.37: 0 ≤ d ≤ cm, own ≤ cm and mis ≤ cm at every vertex. 14.38: the two-colouring statement. "None of them has an exceptional set." "The constant c of SP 14.37 is not explicit." 14.37 and 14.38 are now quoted in §2. | **FIXED** (checked against SP pp. 165–171) |
| N30 | "returns the exceptional set of Cor 14.39" (GAP, wording) | Now "returns an exceptional set of the kind in Cor 14.39, taken with a threshold κ′ ≤ c/3, whenever three conditions hold", followed by the three conditions and the remark that the degree cap matters by SP 14.26. Remark 6.2 adds that X_{κ′} ⊇ X_κ when κ′ ≤ κ, which is correct since the threshold is lower. | **FIXED** |
| N26 | Remark 6.2: "a failure of Target D" | Now "let (G_n) be a failure sequence … for all large n". The hypothesis Δ ≤ (1/2 + c/3)n is replaced by "every vertex of X has degree at most (1 + c)m", which is exactly what (b) needs. | **FIXED** |
| N32 | (R2) "almost every path" (ERROR, wording) | Now "at least (1/4 + β/2)n of the at most n/2 paths, a (1/2 + β)-fraction of them". Problem 7.2 now says "at least", which is correct since a vertex has ≥ ⌈d/2⌉ visits. | **FIXED** |
| N36 | CITATIONS.md lists statements §2 does not reproduce | It now lists 14.24, 14.26, 14.27, 14.37, 14.38 and 14.39 as reproduced, and all six are now in §2. It says 14.30, 14.31, 14.33 and §14.18 are described and credited, and they are. | **FIXED** |
| N24 | Stale PDF ("n/4") | Recompiled; the text has "3n/8", "\|X\| ≤ cm" and "θm/20". | **FIXED** |
| N14 | Step 3 rounding ("101cm") | Now "1.01cm²/⌊m/100⌋ ≤ 102cm" and "104cm + 2 < q". This holds for m ≥ 10,200, inside "m₀ large". | **FIXED** |
| N15 | Step 4: cap q/100, "102\|X\|" (nit) | Unchanged. | open (nit, harmless) |
| N33 | ND §7.2 "Two pieces of the solution are in place … What is missing is only the scheduling"; README "done" (UNCLEAR) | ND §7.2 lines 510–515 are unchanged, including the "within ±D" bound and "the counting obstruction … disappears". The README (Problem 7.1) still says "The one-apex identity and the greedy side-choice are done". connections §D.1 now labels its *other* two observations as heuristic. | **open** (F6 still applies) |
| N37 | [DEC] never referred to | Unchanged. | open (nit) |
| all others | SOUND | Unchanged, or reworded without changing the mathematics: Hypothesis (c) is "automatically satisfied" when X = ∅, ρ = 0; Lemma 3.1 is "SP Lemma 14.28 in our notation"; in the Lean description R is renamed L′. | SOUND |

### 9.2 New material, checked

- **Step 1, new sentence** ("The endpoints of this integer interval are integers … either an endpoint lies in [−0.6q, 0.6q] or the interval contains 0"). Correct: an integer interval with lower end ≤ 0.6q and upper end ≥ −0.6q meets [−0.6q, 0.6q] in an integer.
- **Cor 1.2, proof.** n₀ is now chosen so that m ≥ 17, 1 + γn + cm/2 ≤ cm and (1/2 + γ)n ≤ (1 + c)m. The other facts the proof uses follow automatically:
  - γn/2 = c²n/40 ≤ cm;
  - cm ≥ 2(1 + γn) > 2, so \|b(A) − b(B)\| ≤ 2 ≤ cm;
  - (1/2 − γ)n ≥ m − γ(2m + 1) ≥ (1 − c)m, since γ(2m + 1) ≤ cm;
  - m ≥ m₀, since n₀ ≥ 2m₀ + 2.

  **SOUND.**
- **CKLOT Theorem 1.3.4.** The quote is verbatim against `1factrevision.tex`: the robust-expander definition at line 597 and Theorem `undir_decomp` at line 649, with (i) and (ii) inlined. The theorem is marked unused, correctly.
  - "Derived from Kühn and Osthus": the source says "The next result from [KellyII] (derived from the main result of [Kelly])".
  - "SP uses robust-expander decompositions (through Pfenninger's multigraph version) in its Theorems 14.1 and 14.8, and hence in Corollaries 14.24 and 14.26": correct. SP applies Pfenninger's Theorem 4 in the proof of 14.1 (pdftotext l. 7027) and of 14.8 (l. 7365). 14.24's proof applies Cor 14.9, which comes from 14.8 (l. 8053). 14.26 applies Thm 14.25, whose proof uses "the inputs … detailed in Theorem 14.8" (l. 8112).
  - "Near-bipartite graphs are not robust expanders: a shore S of size n/2 has only about \|S\| robust neighbours": correct for τ ≤ 1/2.
- **SP 14.37 and 14.38 quotes.** Verbatim against pdftotext (p. 170 and p. 171).
- **Credit to SP 14.30** ("the device of threading an exceptional vertex through a preliminary row as u, x, v is SP's own"). Correct: SP's proof of 14.30 says "Replace each labelled pair uv in its preliminary row by u, x, v" (p. 165). ND's partner blocks are this device, with (P2) playing the role of SP's "distinct physical spokes".
- **Credit to SP §14.18** ("for bipartite residuals the identity is SP's counting obstruction \|t(A) − t(B) − D(a − b)\| ≤ 2q"). Correct. Take e_R(A) = e_R(B) = 0 and shore sizes a, b in Lemma 4.1. Then b′(B) − b′(A) = (b − a)D, and with b′ = t − l and \|l(A) − l(B)\| ≤ 2q this is exactly SP's inequality.
- **ND §1.3.** "This goes beyond the o(n) exceptional sets of SP Corollary 14.39, which SP leaves unreturned." Correct.
- **ND §7.2, closing paragraph.** The new sentence "[Problem 7.2] also arises when odd(G) = n − o(n) and some vertex has degree above (1 + c)m" and the cap Δ ≤ (1 + c)⌊n/2⌋ are consistent with (b): a degree above (1 + c)m is (1/2 + β)n with β ≈ c/2 fixed.

### 9.3 A note on `research/connections.md` §D.1

The new line 148 says: "An independent referee pass … found one gap, now fixed: Cor 1.3 needed \|X\| ≤ cm. It also flagged attribution points, now credited: SP 14.30 … SP §14.18". That is accurate as far as Cor 1.3 goes. For the record:
- the attribution points were **not** A17 findings; A17 noted SP §14.18's obstruction only in passing (§5.3);
- A17's other findings (N10, N29, N30, N32, N36, N24) are now fixed;
- N33 remains open.

### 9.4 Verdict at ebfcdd8

**Theorem 1.1, Lemmas 3.1, 3.2, 4.1, 4.2 and 5.1, and Corollaries 1.2 and 1.3 are SOUND as stated.** The Lean file is SOUND.

Open items, none affecting a result:
- **N33.** Relabel the two "pieces in place" of ND §7.2 as heuristics, state the one-apex window \|2(e_R(A) − e_R(B)) + ρD\| ≤ D, and drop or justify "within ±D" and "what is missing is only …". Change the README's "done" to "sketched".
- **connections §D.1, line 136.** Change "This is why …" to "This is the obstruction for the two-apex scheme with the internal edges at X kept".
- **Nits.** N15 (⌊q/100⌋ in (P4)) and N37 (the uncited [DEC]).
