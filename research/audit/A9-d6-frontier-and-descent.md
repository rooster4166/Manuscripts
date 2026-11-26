# Audit A9: d6-frontier, and endpoint-structure Sections 5–6 (descent steps, Fan descent)

Date: 2026-11-26. Referee stance: adversarial. Every result and proof step is graded **SOUND**, **GAP** (fixable; fix given), **ERROR** (false as stated; counterexample given) or **UNCLEAR**.

**Papers.**
- **D6** = `manuscripts/d6-frontier/d6-frontier.tex`, "Hub transfers at deletion degree six" (11 pp. after the fixes below). The scripts are in `manuscripts/d6-frontier/scripts/`.
- **ES** = `manuscripts/endpoint-structure/endpoint-structure.tex`, Section 5 "Two descent steps, and four even vertices" (including "k-step descent" and "Bridges, and reduction to the branching case") and Section 6 "Fan descent, Fan certificates, and the second step for arbitrary pairs". Earlier sections were audited before.

**Version.** The branch moved four times during the audit (aa4134d → 6a4f4c7 → b80c431 → 9623579). D6 did not change except for my fixes. ES gained about 300 lines inside the audited sections: Lemma 28, Theorem 29, Corollary 30, the B⁰_k paragraph, Theorems 43 and 45, Corollary 44, Proposition 47, Conjecture 48, and Remark 49. I audited the final state, commit 9623579 plus my fixes. Numbers below are the printed numbers at that state.

**Note on commits.** This working tree is shared with the parent session, which committed my edits while they were still uncommitted:
- the D6 text fixes went into merge commit 9623579;
- the recompiled D6 PDF went into 61ddca4;
- the ES fixes and their recompiled PDF went into auto-checkpoint 2ed81fa.

All three are pushed. They are exactly the fixes listed in §5. My own commit adds only this report and `A9-scripts/`.

**Scripts and outputs:** `research/audit/A9-scripts/` (see its README).

---

## 0. Headline

1. **D6: no ERROR.**
   - Every Fan step in every table was recomputed by hand. It was then re-checked in an adversarial symbolic model that branches over every donor of every grouped step and every labelled configuration allowed by the hypotheses; free adjacencies are taken present, which is the worst case.
   - All tables pass, and every printed bound is attained in the worst case. Each step has slack exactly 1 (supply = bound + 1).
   - The terminal-step theorems were brute-forced for up to 4 full vertices.
   - The six GAPs are hypotheses or justifications left implicit: no isolated vertex; why the last step of a certificate is single; a shortest-path choice in Cor 4.5(b); a distinctness condition; two abstract or remark omissions. All are fixed in the text.
2. **ES Section 5: no ERROR.**
   - Every Fan application (Lemmas 16, 17, 18, 24, Theorem 19) was recomputed.
   - The new bridge material was checked case by case: gluing Lemma 28, reduction Theorem 29, Corollary 30 ("B_k for all k ≥ 3 ⇒ Gallai"), and the B⁰_k weakening. It is SOUND, and it is formalized (`dstmt_of_branching`, `gallai_of_branching`, `gallai_of_branchBase_three`; no `sorry`).
   - Two GAPs (Lemma 28(2) needs d(t) ≥ 2; Theorem 25 must be read on a fixed vertex set to combine with even-order results) are fixed.
3. **ES Section 6: one ERROR, in the abstract.**
   - The new abstract paragraph says that without connectivity the second step fails only when the even vertices are independent with private odd neighbourhoods, and that "both exceptions" are closed by Theorem 19.
   - This omits Corollary 44(ii). It is false for the paper's own disconnected example P₃ ⊔ (K₅ − e), and Theorem 19 needs connectivity. Scope: the abstract only. Corollary 44, Theorem 45 and Remark 49 are correct. Fix in §4; not applied, per instructions.
4. **ES Section 6: Theorem 45 is redundant.** Its hypotheses are those of Theorem 19 (`two_step_descent`), which gives a stronger conclusion with no exception.
   - The configuration K₃ + r is therefore not an exception for connected graphs. In the paper's own "residual" example, K₆ minus the three edges at r, all three pairs {r, x} are realisable.
   - In the versions up to 6a4f4c7, the "What is left" subsection ended with a false claim: that an argument for these cases "would have to change a Lovász partition inside a fixed graph rather than reduce to a smaller graph". Theorem 19 is exactly such a reduction.
   - That sentence was removed upstream during the audit (b80c431, Remark 49). Remark 49 still credited Theorem 19 to "a parallel workstream" and misdescribed its proof. Fixed.
5. **Lean comparison.** All D6 and ES Lean names cited exist and match the paper's statements. The differences:
   - ES §6 is stated at every order (Remark 32), but Lean keeps even order. The paper discloses this.
   - Remark 32 claimed "everything in this section is formalized". It is not: (S), (C), Corollary 40's classification, Corollary 44, the assembly of Theorem 45, (O2), (O3) and the cut-vertex criterion are not formalized. Fixed.
   - The ES §5 Formalisation remark does not mention `Bridge.lean` or `BranchBase.lean`. This is an omission, not fixed: that workstream is active.
   - No D6 result is formalized yet; D6 §9 only describes the intended Lean shape, and says so.

---

## 1. Summary verdict table

### 1.1 D6 (d6-frontier)

| # | Result / step | Verdict | Note |
|---|---|---|---|
| D1 | §1 setting: standard profile (6 ends on U, three doubled) | SOUND; **GAP-1 fixed** | Needs B without isolated vertices (seeds, and \|Od(B)\| = 2k − 6). Now stated in "The test" and in Thm 6.1 |
| D2 | Inputs (A), (B), (C) vs Lean | SOUND | `LovaszStatement`; `realisable_evenSet_erase` (even order, `∀ v, 0 < degree v`); `fan_grouped` / `fan_single` match Lemma 2.1 exactly (v ∉ S, S non-adjacent in the current graph, strict inequality) |
| D3 | Lemma 2.1 (Fan) | SOUND | Statement = `fan_grouped` |
| D4 | Lemma 2.2 (seeds) | SOUND | (b) has (\|G\| − 2)/2 + 1 = \|G\|/2 paths |
| D5 | Certificate shape | SOUND | |
| D6 | Lemma 2.3(a) forward relay | SOUND | Bound ≤ 1 because v_{i−1} carries 2 ends |
| D7 | Lemma 2.3(b) carry | SOUND | Blanks are B₀ ∪ {v_i}; v_i is not its own neighbour |
| D8 | Thm 3.1 terminal step | SOUND | Excess sum 6, β ≥ 3; all three cases re-derived; brute force with \|F\| ≤ 4 |
| D9 | Thm 3.2 leaf form | SOUND | β = 5 is forced in the odd case, so no "some b(w) ≥ 2" hypothesis is needed |
| D10 | Cor 3.3 | SOUND; **GAP-2 fixed** | Thm 3.1 covers single steps only. The last step of any certificate is single, because a grouped offer needs one held edge per donor. Added. Also "passes through" → "ends at" |
| D11 | Rem 3.4 (induction on full vertices) | SOUND (heuristic) | Class preservation checked |
| D12 | Rem 3.5 (hub capacity) | SOUND (heuristic) | ⌈m/2⌉ receipts; the root hub is short by 1 and the full hub by 2 |
| D13 | Thm 4.1(i) | SOUND | 6 steps, 192 adversarial branches; worst \|Z\| = 0, 1, 2, 4, 3, 2 against supplies 1, 4, 3, 5, 4, 3 |
| D14 | Thm 4.1(ii) | SOUND | 7 steps, 48 branches; N(a) ∩ T may contain q, which is handled |
| D15 | Thm 4.1(iii) | SOUND | 6 steps, 8 branches; no degree hypothesis needed |
| D16 | Remark after 4.1 (novelty, overlap with INC) | UNCLEAR (novelty not checked); arithmetic SOUND | |
| D17 | Thm 4.3 (two resources) | SOUND | 9 steps, 9,264 branches; the C-trick at step 4 is correct |
| D18 | Thm 4.4 (relay) | SOUND | m = 1..4, 372 branches each |
| D19 | Cor 4.5 (residual constraints) | (a), (c), (d) SOUND; (b) **GAP-4 fixed** | (b) needs a shortest path to get a ∉ N(c_i) for i < m. Then a ∉ N(r) and oddness are automatic |
| D20 | Thm 5.2, two batteries | SOUND | 12 steps, every root, 360 branches |
| D21 | Thm 5.2, battery + pendant | SOUND | 10 steps, 360 branches. Not replayed by the paper's scripts; table now says so |
| D22 | Rem 5.3 (false-twin example) | SOUND | Hypotheses of §§4–5 fail; all 20 triples realisable (rerun) |
| D23 | Thm 6.1(a) root hub, all d | SOUND | d = 4, 6, 8, 10 at minimal β; with β − 1 it fails (d = 8, 10), so the count is tight |
| D24 | Thm 6.1(b) full hub, all d | SOUND; **GAP-5 fixed** | Pendant must be distinct from the battery vertices; no isolated vertex |
| D25 | Remark after 6.1 (d = 4, d = 8) | SOUND; **GAP-6 fixed** | d = 4 needs an odd neighbour of degree ≥ 3. FHZ consistency is external (not checked); novelty UNCLEAR |
| D26 | Prop 7.1 (no single-stage full-pair program) | SOUND within its stated model | Exhaustive AND–OR search, rerun identical; minimal donor sets are WLOG. Model: only spokes move, exterior never blank |
| D27 | §8 Closed / Not closed | SOUND | Table 1 lists Thms 4.3 and 4.4 under "D = ∅"; they need only Q = ∅ (understatement) |
| D28 | §8 limitation (1) | SOUND | Verified: adversarial z₂, z₃ defeat every first donor p; with controlled donors it succeeds |
| D29 | §8 Observation | SOUND (evidence only) | Rerun identical |
| D30 | §9 formalization notes | SOUND | Describes the intended shape only; cited names exist (`sum_ends`, `ends_mod_two`, `ends_eq_of_tight`, `Realises.size_eq`) |
| D31 | Computational checks section | SOUND; **note fixed** | All scripts rerun, assertions pass. Replays follow the engine's donor, so they are not adversarial; the text now says so |
| D32 | Abstract item (2) | **GAP-3 fixed** | Omitted d(r) ≥ 8 and d(y) ≥ 3 |

### 1.2 ES Section 5 (two descent steps; k-step descent; bridges)

| # | Result / step | Verdict | Lean |
|---|---|---|---|
| E1 | Conventions, Z_D(u), eq. (2) | SOUND | |
| E2 | Lemma 15 (Fan's transfers) | SOUND | = `fan_grouped` |
| E3 | Lemma 16 (edge) | SOUND: Z_D(s) = ∅, b_D(t) = 1 | `realisable_of_edge` matches |
| E4 | Lemma 17 (star) | SOUND: 0 < 1; \|Z\| ≤ 1 < 2; \|Z\| ≤ 2 < 3 | `realisable_of_star` matches |
| E5 | Lemma 18 (lift) | SOUND | `realisable_lift` matches |
| E6 | Thm 19 (two descent steps) | SOUND: all three Case 1 subcases and the Case 2 induction (w ∈ Ev(K), w ≠ t, P − y in K, no isolated vertex) | `two_step_descent` matches (connected, even order, e ≥ 4) |
| E7 | Connectivity example P₃ ⊔ (K₅ − e) | SOUND (computed) | |
| E8 | Cor 20 and its equivalent forms | SOUND | `emc_four` |
| E9 | Thm 21 (rank-2 matroid) | SOUND | `endpoint_matroid_four` (bases, loopless, minimal sets). The "≤ 2 parallel classes" clause is not in Lean |
| E10 | Two-triangle example | SOUND (computed: p = 3, realisable pairs exactly the 4 cross pairs) | |
| E11 | Cor 22 (rooted test, e = 4; BP₃) | SOUND | `rooted_four`, `rooted_le_four` |
| E12 | Remark "Six even vertices" | SOUND | |
| E13 | k-step definition | SOUND | `Desc` |
| E14 | Lemma 24 (general transfer) | SOUND | `realisable_transfer` |
| E15 | Thm 25 (connected reduction) | SOUND; **GAP-7 fixed** | `desc_reduction` is on a fixed vertex type. The paper's "every connected graph" form must be read that way to combine with even-order results (Cor 27, the 3-step reduction). Sentence added |
| E16 | Example (K₅ − e) ⊔ (K₅ − e) | SOUND (computed) | |
| E17 | Thm 26 (one even neighbour) | SOUND | `desc_succ_of_unique` |
| E18 | Cor 27 (three steps) | SOUND (no written proof; follows from Thm 26 with k = 2 and the inductive statement of Thm 19, as the preceding sentence says) | `desc_three_of_unique` |
| E19 | Deletion-test sentence and 3-step reduction | SOUND (with GAP-7) | `desc_three_reduction` |
| E20 | Lemma 28(1) bridge gluing | SOUND | `glue_bridge` |
| E21 | Lemma 28(2) | SOUND; **GAP-8 fixed** | If d(t) = 1, G[B] = {t} and "t is an end of a path of D_B" fails. Thm 29 uses d(t) ≥ 2 |
| E22 | Thm 29 (reduction to the branching case) | SOUND | `dstmt_of_branching` |
| E23 | Cor 30 (B_k ∀ k ≥ 3 ⇒ Gallai; B₃ ⇒ (R) at e = 6) | SOUND | `gallai_of_branching` via `gallai_iff_rootedTest` |
| E24 | B⁰_k paragraph | SOUND (proof adapts: Case 2 first, no w) | `BranchBase` matches B⁰_k. The k ≥ 3 form is `gallai_of_branchBase_three`; the paper names `gallai_of_branchBase` |
| E25 | Formalisation remark (§5) | SOUND for what it lists | Omits Bridge.lean / BranchBase.lean (not fixed) |

### 1.3 ES Section 6 (Fan descent, certificates, pair step, obstructions)

| # | Result / step | Verdict | Lean |
|---|---|---|---|
| F1 | Remark 32 (Lemmas 3, 4 at every order) | Math SOUND; **GAP-9 fixed** | The claim "everything in this section is formalized" was false (see README). Replaced by an accurate list |
| F2 | Tight graphs, dictionary | SOUND | |
| F3 | Lemma 34 (Fan 3.4) | SOUND | = `fan_single` |
| F4 | Lemma 35 (Fan descent) | SOUND | `realisable_erase_of_fan` |
| F5 | Lemma 36 (Fan transfer) | SOUND (also when d(w) = 1) | `realisable_of_fan_transfer` |
| F6 | Thm 37 (second step) | SOUND at every order (exhaustive ≤ 7 vertices, odd orders included). It is Lemma 16 with (s, t, u′) = (w, u, v) | `realisable_evenSet_erase_pair` (even order) |
| F7 | Cor 39 (non-realisable pairs are E-twins) | SOUND | `etwin_of_not_realisable` |
| F8 | Twin equivalence; K₂,₄ + e example | SOUND (example computed) | |
| F9 | Cor 40 (four E-subgraphs) | SOUND; **GAP-10 fixed** | Closing sentence now says that Thm 19 removes all exceptions for connected G |
| F10 | Fan certificates; Thm 41 (soundness) | SOUND | `FanCert`, `realisable_of_fanCert` (odd ∧ 1 < degree ⇔ d(w) ≥ 3) |
| F11 | Even-step lists = semi-induced matchings | SOUND (the w_i are automatically distinct) | `FanSchedule` |
| F12 | Cor 42 | SOUND | |
| F13 | Thm 43 (pair step) | SOUND: grouped donor t adversarial; zero-end neighbours of t′ ⊆ {t, u} | `realisable_pair` matches |
| F14 | Cor 44 | Statement SOUND; **GAP-11 fixed** | Proof skipped e = 5, possible at odd order |
| F15 | Thm 45 (goal (b)) | SOUND, but **redundant**: Thm 19 has the same hypotheses and a stronger conclusion with no exception | step: `realisable_of_oddPath` |
| F16 | Paragraph after Thm 45 | SOUND; **GAP-12 fixed** | Did not mention that Cor 20 already gives the e = 4 case with no exception |
| F17 | Prop 46 (L), (S), (C) and the bullet list | SOUND (exhaustive ≤ 7 vertices; G₀^{N(u)} and path iteration checked by hand) | (L) partly (`realisable_leaves_singleton`); (S), (C) not |
| F18 | Prop 47 (O1)–(O3); edge-bound remark | SOUND | (O1) = `degree_le_of_tight` |
| F19 | Cut-vertex criterion | SOUND (both directions) | |
| F20 | Census (orders 4, 6, 8) | SOUND: reproduced exactly | |
| F21 | Conj 48 | Conjecture (consistent with the census) | |
| F22 | "(O1) impossible for G^{Ev∖{u,v}}" | SOUND | |
| F23 | "What is left" subsection | SOUND at the audited state. The pre-b80c431 closing sentence was an ERROR (contradicted by Thm 19) and is gone | |
| F24 | Remark 49 | **GAP-13 fixed** | Credited Thm 19 to "a parallel workstream … base branch" and described it as a y–w path induction via Lemma 35. It is Thm 19 of this paper: a path from y to any even vertex, using Lemmas 16, 17, 18 |
| F25 | **Abstract, second paragraph** | **ERROR** (§4) | |
| F26 | §7 computational paragraph (Section 6 part) | SOUND as revised ("order 8: running"). For connected graphs the claim follows from Thm 19 anyway | |

Totals:
- **D6:** 0 ERROR, 6 GAPs fixed, plus one note on the replays.
- **ES §5:** 0 ERROR, 2 GAPs fixed.
- **ES §6:** 1 ERROR (abstract; not edited), 5 GAPs fixed (GAP-9 to GAP-13), 1 redundancy (Theorem 45).

---

## 2. D6: step-by-step details

### 2.1 Conventions and inputs

Lemma 2.1 is `fan_grouped` verbatim: `u ∉ T`, `∀ t ∈ T, ¬K.Adj t u`, and `#{w : K.Adj u w ∧ ends w = 0} < ∑_T ends`. The conclusion holds for every graph with edge set E(K) ∪ {tu}.

Lemma 2.2 needs B₀ to have even order and **no isolated vertex**:
- (a) Lovász gives ⌊N/2⌋ paths; with all N vertices odd, each has exactly one end.
- (b) Lemma 3 (`realisable_evenSet_erase`) gives o/2 + 1 = |G|/2 paths.

Each theorem's held set keeps every touched vertex at positive degree (checked below). Untouched vertices of B keep their degree, so B itself must have no isolated vertex. The paper never says this (abstract: "connected"). **GAP-1, fixed:** "Throughout, B has even order 2k and no isolated vertex …", and likewise in Thm 6.1. The excess count of Thm 3.1 (Σε = 2k − |Od| = 6) needs the same hypothesis.

Lemma 2.3:
- **(a)** After v_{i−2} → v_{i−1}, v_{i−1} has 2 ends, so the next step needs bl ≤ 1. The edge v_{i−1}v_i is absent (the path is simple and its edges are not in H). SOUND.
- **(b)** Each receiver v_i has b = 0 at its turn but is not its own neighbour. The blanks are B₀ ∪ {v_i}. SOUND.

### 2.2 Terminal step (Thms 3.1, 3.2; Cor 3.3)

**Thm 3.1.** Write b for the final ends, b_{D′} = b + e_u − e_v, and ε for the excess (b on U, b − 1 on odd vertices). Then ε is even and nonnegative, and Σε = 6.

- With Z the blank set of U and β = |Z|, we have 2(6 − β) ≤ 6, so β ≥ 3.
- v ∈ L is adjacent to U − v and v ∉ Z. Every w ∈ Z − u is a blank neighbour of v in B − e (wv ≠ e since w ≠ u). This gives (2): b(u) + 1 > |Z − u|.
- **u ∈ Z:** β ≤ 1, impossible.
- **u ∈ U − Z:** β ≤ b(u) ≤ 2β − 4, so β ∈ {4, 5}, which gives (α) or (β).
- **u ∈ F:** 2 + 2a > β and a ≤ β − 3, so β ≥ 5. With the hypothesis this forces β = 5 and a = 2, which is (γ).
- The receiver must have b ≥ 1 and no excess, unless it is w. All correct.

**Thm 3.2.** Excess 4, |T| = 5.
- u ∈ T − Z gives β = 4 and b(u) = 4.
- u odd gives β = 5, so all of T is blank. This is why Thm 3.2 needs no "b(w) ≥ 2" hypothesis. SOUND.

**Brute force** (`terminal_more.py`, reusing the paper's `survivors`): one, two, three or four full vertices (F independent or a clique), and the W-form with r plus 0, 1, 2 or 3 full vertices. Only hub profiles survive.

**Cor 3.3, GAP-2.** Thm 3.1 is about a *single* last step, but certificates also use grouped steps. The missing argument:
- In a grouped offer S → v inside a certificate, each potential donor s must be the far end of a held edge sv. Otherwise H + sv ⊄ B.
- At the last step only one held edge is left, so |S| = 1.
- Added to the text. "Passes through a hub profile" now reads "ends at".

### 2.3 Root hubs: recomputed Fan counts

Notation: supply / worst-case |Z| (over all labelled configurations and all donors, from `A9-scripts/worst.txt`) / printed bound. In every row the worst case equals the printed bound, and supply = bound + 1.

**Thm 4.1(i).** Held: rT and ry.
- B₀: d(r) − 6 ≥ 2 (needs d(r) ≥ 8), d(y) − 1 ≥ 2 (needs d(y) ≥ 3), T odd, so Ev(B₀) = {r, y}.

| step | transfer | supply | worst \|Z\| | printed | blank set and current adjacency |
|---|---|---|---|---|---|
| 1 | p → r | 1 | 0 | 0 | blank y; ry held |
| 2 | (T−p) → r | 4 | 1 | 1 | p (rp now present) |
| 3 | (T−p−z₂) → r | 3 | 2 | 2 | p, z₂ |
| 4 | r → s₁ | 5 | 4 | 4 | Z ∪ {y}; s₁ = p′ if p′ ∉ Z |
| 5 | r → s₂ | 4 | 3 | 3 | Z; s₂ ∉ N(y) because N(y) ∩ T ⊆ {p, p′} and p ∈ Z |
| 6 | r → y | 3 | 2 | 2 | N(y) ∩ Z ⊆ {p, p′} |

The donors z₂, z₃ are adversarial. The ordering rule (s₁ = p′ when p′ survives) handles every choice: 192 branches. SOUND.

**Thm 4.1(ii).** Held: r(T − q), ra, rb, ab.
- r loses 6, so d(r) ≥ 8 is needed; a and b lose 2 and stay odd.
- Seed: b(r) = 2, b(q) = 0. q ∉ N(r) ∪ N(b).
- Steps 1–7: supplies 1, 1, 1, 3, 5, 4, 3; worst |Z| 0, 0, 0, 1, 4, 3, 2 (printed: same).
- |N(a) ∩ T| ≤ 2 may include q. Then N(a) ∩ (T − q) ⊆ {z₁}, which is only easier. SOUND.

**Thm 4.1(iii).** Held: rN_T(r), ra, rb, ab.
- r loses 5 and stays odd with degree ≥ 1, so no degree hypothesis is needed.
- Seed: b(q₁) = 2, b(q₂) = 0, b(r) = 1. b ∌ q₂.
- Supplies 1, 1, 1, 2, 4, 3; worst 0, 0, 0, 1, 3, 2. Final b(r) = 1 + 1 + 1 + 1 − 1 − 1 = 2. SOUND.

**Thm 4.3.** Held: rT, ry, ra, rb, ab.
- r loses 8, so d(r) ≥ 10 is needed.
- Steps 1–9: supplies 1, 1, 1, 2 or 4, 3, 6, 5, 4, 3; worst |Z| 0, 0, 0, 1, 2, 5, 4, 3, 2 (printed: same).
- The step-4 offer P₂ = C (when |C| = 2) guarantees |C ∩ (T − Z)| ≤ 1 for every donor, so a single receiver can see both parked vertices. C ⊆ T − z₁ because z₁ ∉ N(a). 9,264 branches. SOUND.

**Thm 4.4.** Held: rT and the path.
- r loses 6; each c_i loses 2 (odd, degree ≥ 3 before); a loses 1 (needs d(a) ≥ 3).
- Steps: z₁ → r (1/0), (4/1), (3/2), r → s₁ (5/3), r → s₂ (4/3), r → c₁ (3/2), then c_i → c_{i+1} and c_m → a (2/0 each).
- c₁ does not see a: either c₁a is the held path edge (m = 1) or a ∉ N(c₁). m = 1..4, 372 branches each. SOUND.

**Cor 4.5.**
- (a) Contrapositive of 4.1(i): d(r) ≥ 10 ≥ 8 and δ ≥ 3 give d(y) ≥ 3.
- (c) Contrapositive of 4.3.
- (d) Contrapositive of 5.2.
- (b) GAP-4. Thm 4.4 also needs a ∉ N(c_i) for i < m, a ∉ N(r), and the path vertices odd. Take a shortest path from c to the set of vertices with no core neighbour, through such vertices. A shortcut c_i a with i < m would contradict minimality. Vertices with no core neighbour lie outside U = Ev(B), so they are odd, and they are not adjacent to r ∈ U. Fixed.

### 2.4 Full hubs (Thm 5.2) and all d (Thm 6.1)

**Two batteries.** Held: xU and both triangles.
- x loses 10. d(x) ≥ 11 holds automatically (odd, at least 10 neighbours).
- Seed: all odd, b ≡ 1.

| step | transfer | supply | worst \|Z\| | printed |
|---|---|---|---|---|
| 1, 2 | b₁ → x, a₁ → b₁ | 1, 1 | 0, 0 | 0, 0 |
| 3, 4 | b₂ → x, a₂ → b₂ (a₁b₂ ∉ E) | 1, 1 | 0, 0 | 0, 0 |
| 5–7 | (U−r) → x ×3 | 5, 4, 3 | 0, 1, 2 | 0, 1, 2 |
| 8–10 | x → r, s₁, s₂ | 6, 5, 4 | 3, 3, 3 | 3 |
| 11, 12 | x → a₁, x → a₂ | 3, 2 | 1, 0 | 1, 0 |

No a₂b₁ condition is needed, which is correct: at step 2 the only blank is b₁ itself. Every root passes; 360 branches. SOUND.

**Battery + pendant.**
- x loses 9, so it needs a neighbour outside U ∪ {a₁, b₁, y} (stated); y loses 1.
- Supplies 1, 1, 5, 4, 3, 6, 5, 4, 3, 2; worst 0, 0, 0, 1, 2, 3, 3, 3, 1, 0. SOUND.
- The paper's replay script does not cover this form. Table entry corrected.

**Thm 6.1(a).**
- Receipts: j-th supply d − 1 − j > j for j < d/2.
- Donations: i-th supply 2 + β + d/2 − i > d/2 needs i ≤ β + 1, and i ≤ d/2 − 2 ≤ β + 1 by β ≥ d/2 − 3.
- Paybacks: supply β + 3 − j against ≤ β − j.
- All correct (0-indexed). The model check passes at d = 4, 6, 8, 10 with β = max(0, d/2 − 3). With one battery fewer it fails at the first donation that has supply = d/2 (d = 8, 10). The counts are therefore tight for this certificate.

**Thm 6.1(b).** Same check at β = d/2 − 1, and pendant form with β = d/2 − 2. GAP-5: the pendant y must be distinct from the battery vertices, as Thm 5.2 states. Fixed.

**Remark after 6.1.** The d = 4 bounds (4 against 3, then 3 against 2) are right with no quietness. "At least three odd neighbours" is d(r) ≥ 6, but the seed also needs one odd neighbour of degree ≥ 3 (GAP-6, fixed).

### 2.5 Prop 7.1 and §8

`stage_search.py`:
- **Restriction to minimal donor sets.** Restricting grouped offers to inclusion-minimal donor sets is WLOG (fewer branches, each a branch of the superset). Testing single removals suffices because all b ≥ 1.
- **Success criterion.** It requires the exact restored vector.
- **Sanity check.** It reproduces Lemma 4 for five-contact pairs.
- **Rerun.** Identical output in 3.6 s.

The claim is exactly about this model (spokes only, exterior never blank, a single stage). SOUND.

§8 (1) was checked in the adversarial model (`limit1.py`). With |N(y) ∩ T| = 3, no choice of the first donor p survives adversarial z₂, z₃ for any order of the three donations. With controlled z₂, z₃ the certificate exists.

### 2.6 Scripts

| script | rerun result | what it really checks |
|---|---|---|
| `test_engine.py` 1, 2 | 400 + 400 instances, pass | Engine output valid and end vector as predicted whenever Fan's inequality holds |
| `terminal_check.py` | Same counts (examples differ by hash order) | Thms 3.1, 3.2 for ≤ 2 full vertices |
| `replay_root_hub.py` | 10/10 | One concrete graph per seed; the engine's donor at grouped steps. Seed 10's blank counts differ from the stored `.out` (CP-SAT nondeterminism in the seed); assertions pass |
| `replay_shapes.py` | 8/8, identical | Uses bound 3 at every donation (stricter than the printed 4 in step 5 of (ii)) |
| `replay_two_resources.py` | 4/4, identical | |
| `replay_relay.py` | 5/5, identical | m = 1, 2 |
| `replay_full_hub.py` | 3 × 6, identical | Two-battery form only |
| `replay_general_d.py` | 3/3, identical | d = 8 only (the docstring's "d = 6 for comparison" is not run) |
| `stage_search.py` | identical | Prop 7.1 (exhaustive in the model) |
| `small_observation.py` | identical | 10 graphs, all triples realisable |

**Limitation.** The replays are concrete instance checks along one donor branch. They do not test the adversarial reasoning; `A9-scripts/check_tables.py` does. Sentence added to D6.

---

## 3. ES Section 5: details

**Lemmas 16, 17, 18, 24.** Each Fan application was recomputed.
- Lemma 16: Z_D(s) = N_K(s) ∩ {u′} = ∅ and b(t) = 1.
- Lemma 17:
  - Step 1: Z = ∅, supply 1.
  - Step 2: Z_{D₁}(y) = {w}, because yw is now present; supply 2.
  - Step 3: Z_{D₂}(t″) ⊆ {w, t′}; supply b(y) = 3.
  - All donors are non-adjacent to the receiver in the current graph.
- Lemma 18 and Lemma 24: Z = ∅ by (2), and the supply is 2, resp. 1.

**Thm 19.**
- Case 1, all three subcases: the triples passed to Lemma 16 are distinct even vertices with the stated adjacencies.
- Case 2:
  - t is odd and has a further edge on P, so K has no isolated vertex.
  - w ≠ t (parity) and w ∈ Ev(K); |Ev(K)| = e.
  - P − y is a shorter path in K from t to an even vertex.
  - The returned v satisfies v ≠ t, so t ∈ S. {w, v} are even in G, hence not adjacent to y.
- Lean `two_step_descent` matches.

**Thm 25 (GAP-7).** The proof is right, but the paper states it for "every connected graph", while Cor 27 and the 3-step reduction hold for even order. The induction keeps the vertex set (K = G − yt), so the fixed-vertex-set (fixed even order) version holds verbatim. That is the form of `desc_reduction`. Sentence added.

**Thm 26.**
- K = G − yt has ≤ 2 components, so two even vertices share one.
- The choice of y′ and w′ is valid in both cases w ≠ t and w = t.
- W ⊆ Ev ∖ {y, t} is non-adjacent to y, so Lemma 24 applies. R = W ∪ {t}.

**Lemma 28.**
- (1) The joined path P_A·yt·P_B is a path because the sides are disjoint. y keeps b_{D_A}(y), t keeps b_{D_B}(t), and both leaf ends vanish.
- (2) GAP-8. If d(t) = 1, then G[B] = {t} has no paths, so no path ends at t. The conclusion still holds by adding yt as a new path, but the written proof fails. Thm 29 applies it only with d(t) ≥ 2. Hypothesis added.

**Thm 29.** Checked case by case.

- **Pieces.**
  - Each piece has even order, no isolated vertex (y keeps degree ≥ 1; t has degree ≥ 1 since d(t) ≥ 2), and is connected.
  - Each has fewer edges, because both sides have edges.
  - Capacities |Ev(piece)|/2 are integers.
  - The piece containing w has ≥ 2 even vertices, hence capacity ≥ 1.
- **Totals.**
  - |A| odd: Σ capacities = e/2 ≥ k + 1.
  - |A| even, t even: (e − 2)/2 ≥ k, with t removed automatically.
  - |A| even, t odd: e/2 ≥ k + 1, with t kept in G[B], so t ∈ S_B as Lemma 28(2) requires.
- **Choosing the r's.** A greedy choice (w's piece first) satisfies all constraints.
- **Applying D_r.** It needs a kept vertex and a w′ in the piece; r ≥ 1 gives ≥ 2 even vertices. The outer hypothesis covers r ≤ k; the inner induction covers r = k + 1 on fewer edges.
- **Case 3.** Thm 26's argument with D_k in the connected K; e − 2 ≥ 2k.
- **Case 4.** Not Case 1 and not Case 3 means y has no even neighbour. Indeed, if y had exactly one even neighbour t and yt were a bridge, Case 2 would apply, since d(t) ≥ 2.
  - Not Case 2 then means every bridge at y is pendant.
  - A star centred at y has e ≤ 1, so some edge yt is neither pendant nor a bridge.
  - Thm 25's step with the inner induction finishes the case.
- **Verdict.** SOUND. `dstmt_of_branching` (no `sorry`) has the same statement (`DStmt`, `BStmt` over all finite types, connected, even order, 2j ≤ |Ev|).

**Cor 30 and the B⁰_k paragraph.**
- For a critical H with e = 2k, D_k gives (R).
- The Gallai ⇔ rooted-test step is in Lean (`gallai_iff_rootedTest`), so `gallai_of_branching` is fully formal given B_k.
- Without w, the proof of Thm 29 runs with Case 2 placed before Case 1, which yields exactly B⁰_k (`BranchBase`, which takes `Desc H k y ∅`).

---

## 4. ES Section 6: details, and the ERROR

**Lemmas 35 and 36.**
- Lemma 35: the only zero-end vertices of D′ are Ev ∖ S, and none of them is a neighbour of w. Supply b(u) = 1 > 0. Sizes match.
- Lemma 36: a zero-end neighbour x of w in G′ would lie in Ev ∖ S with x ≠ u. The lemma holds even if d(w) = 1 (w isolated in G′).

**Thm 41.**
- In the even step, X ∖ {x} ⊆ Ev(G − xw) because w ∉ X, and Lemma 35's hypothesis is "w has no neighbour in X ∖ {x}".
- In the odd step, Ev(G − xw) ∖ ((X ∖ x) ∪ {w}) = Ev ∖ X.
- Degrees stay positive.
- In even-step lists, x_kw_i ∉ E for k < i forces the w_i to be distinct, since w_i = w_l with l < i would give x_lw_i ∈ E.

**Thm 43.**
- G₂ = G − aw − a′w has no isolated vertex.
- The grouped offer {a, a′} at w has supply 2 against ≤ 1 (only u can be blank).
- Then the single return of t′w to t′ has zero-end neighbours ⊆ {t, u}, with supply 3 (w even) or 2 (w odd).
- The odd hypothesis "aa′ ∉ E or neither a nor a′ ∼ u" is exactly what an adversarial t requires.

**Cor 44 (GAP-11).** Section 6 allows odd order, so e = 5 is possible. In the "complete" case the proof treats only e ≥ 6 and e = 4. With e = 5 the argument works, because d(w) ≥ e − 2 = 3 and w is even, so d(w) ≥ 4. Text changed to e ≥ 5. The statement was correct.

**Thm 45 (redundant).**
- The proof is correct: the minimal-distance pair, the parity of interior vertices, the D = 2 argument, and the certificate (odd transfers along p₁ … p_{D−1}, then the even step into t).
- But Thm 19 with y = r and w = any other even vertex gives the conclusion with no exception, under the same hypotheses (connected, even order, e ≥ 4).
- Check: K₆ minus the three edges at r (the paper's residual example) has all three pairs {r, x} realisable (`k3r.py`). So do all connected graphs of order ≤ 6 with G[Ev] = K₃ + r.
- Remark 49 (merged during the audit) says this, but attributed Thm 19 to another workstream (GAP-13, fixed). The paragraph after Thm 45 now notes that Cor 20 already covers e = 4 (GAP-12).

**Exhaustive check** (`es_exhaust.py`; all 1,043 graphs with ≤ 7 vertices and no isolated vertex, all orders, not necessarily connected). No violation of:
- Remark 32 (Ev and every Ev ∖ {u} realisable; 3,515 instances);
- Cor 39 (5,449 pairs);
- Prop 46 with X = {x, v}: (L) 676, (S) 2,420, (C) 1,400 instances.

**Prop 47, cut vertices, census.**
- (O1): d + b ≤ 2|D|, so d ≤ n − 3 for odd vertices.
- (O2): a forced triangle.
- (O3): three distinct paths through y force b(y) = 3.
- Cut-vertex criterion:
  - (⇒) Cut the crossing paths at c; then |b₁ − b₂| = |e₁ − e₂| = β(c).
  - (⇐) Glue min(b₁, b₂) pairs; the path count is |Od|/2.
- The census was reproduced exactly with independent code (`census.py`):
  - order 4: 3 two-even graphs, 2 non-tight (both (O1));
  - order 6: 47, with 17 non-tight (16 (O1), 1 (O2));
  - order 8: 2,668, with 372 non-tight (344 (O1), 21 (O2), 4 (O3), 3 cut).
  - No 2-connected non-tight graph outside (O1)–(O3).

**ERROR (abstract, second paragraph).** The text reads:

> "Without connectivity, faithful descent therefore takes its second step except when the even vertices are independent and have private odd neighbourhoods; both exceptions are closed by the path induction of Theorem 19 (Remark 49)."

What is wrong:
- (a) Only one exception is listed. Cor 44(ii) (e = 4, G[Ev] = K₃ + r) is missing.
- (b) The first clause is false. Take the paper's own example G = P₃ ⊔ (K₅ − e) and let r be the middle vertex of P₃.
  - G[Ev] = K₃ + r is not edgeless.
  - No pair containing r is realisable: p(K₅ − e) = 3, confirmed by computation.
  - So for every u the second step from Ev ∖ {u} keeping r fails.
- (c) Thm 19 needs connectivity. "Both exceptions are closed" holds only for connected G; without connectivity both exceptions genuinely occur.

Scope: the abstract only. Cor 44, Thm 45 and Remark 49 state the correct facts.

Suggested fix (not applied): "Without connectivity, faithful descent therefore takes its second step except in the two configurations of Corollary 44; for connected graphs Theorem 19 closes both (Remark 49)."

**Resolved upstream during the audit.** At 6a4f4c7 the "What is left" subsection ended:

> "An argument for them would have to change a Lovász partition inside a fixed graph (an exchange) rather than reduce to a smaller graph."

For connected graphs this is false: Thm 19 (Lean-verified) settles both configurations by edge deletion and a path induction. Commit b80c431 removed the sentence.

---

## 5. Fixes applied

**D6** (text in 9623579, PDF in 61ddca4; see the note at the top):
1. "The test": B has no isolated vertex (GAP-1). Thm 6.1: the same.
2. Abstract (2): d(r) ≥ 8 and d(y) ≥ 3 (GAP-3).
3. Cor 3.3: why the last step is single; "ends at a hub profile" (GAP-2).
4. Cor 4.5(b): take a shortest path (GAP-4).
5. Thm 6.1(b): pendant distinct from the battery vertices (GAP-5).
6. Remark after 6.1: one odd neighbour of degree ≥ 3 (GAP-6).
7. Computational checks: replays follow the engine's donor; the full-hub replay covers the two-battery form only.

**ES** (in 2ed81fa):
1. Thm 25: fixed-vertex-set form (GAP-7).
2. Lemma 28(2): d(t) ≥ 2 (GAP-8).
3. Remark 32: accurate formalization list (GAP-9).
4. Cor 40 closing sentence: Thm 19 removes all exceptions for connected G (GAP-10).
5. Cor 44 proof: e ≥ 5 (GAP-11).
6. After Thm 45: Cor 20 already covers e = 4 (GAP-12).
7. Remark 49: it is Thm 19 of this paper, with a correct description (GAP-13).

Both PDFs were recompiled with pdflatex, twice each. No undefined references.

**Not applied:**
- The abstract ERROR (§4).
- Optional: name Bridge.lean and BranchBase.lean in the ES §5 Formalisation remark, and use `gallai_of_branchBase_three` for the k ≥ 3 form.
- Optional: D6 Table 1, "D = ∅" → "Q = ∅" for Thms 4.3 and 4.4.
- The TwoEven.lean docstrings cite outdated theorem numbers ("Theorem 26", "Theorem 28" for the pair and path steps; now 43 and 45).
