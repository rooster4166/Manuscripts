# A10 — Referee audit: the jm-repair manuscript (repaired JM Theorem 8, transfer lemma, Wu's conjecture)

Auditor: independent adversarial referee pass, 2026-11-26.

Source audited:
- **[REP]** "Rainbow Hamiltonian cycle decompositions: repairing the extension step in the Javadi–Miralaei proof of Wu's conjecture", `manuscripts/jm-repair/jm-repair.tex`, 16 pp. I audited the version of commit 46410cd (merged as d440b05), which already contains the author's internal-referee revisions, and checked every change against the earlier versions I had read first (at efe9e1a and f1d0af8). Numbers such as "Lemma 5.1" refer to the compiled PDF.
- **[JM]** R. Javadi, M. Miralaei, arXiv:2403.17290v1. I compared [REP]'s account of Theorems 5, 7 and 8 and Claim 12 with the arXiv text, using the copy downloaded for A4.
- **[OSC]** `gallai/01-original-manuscripts/odd-semi-clique-boundary.pdf`, text extracted with pdftotext, for the downstream use.
- **[A4]** `research/audit/A4-semi-cliques-JM.md`, §2.

The author's "internal referee" (its comments and `scripts/independent/`) is treated as **non-independent**. Every verdict below rests on my own line-by-line re-derivation and on my own scripts in `research/audit/A10-scripts/`, which share no code with the manuscript's scripts.

Verdicts: **SOUND**; **GAP** (fixable; the fix is stated); **ERROR** (false; a counterexample is given); **UNCLEAR** (cannot be settled from the available material).

---

## 0. Summary table

| # | Item ([REP] location) | Verdict | Note |
|---|---|---|---|
| P1 | Lemma 2.1: each vertex has exactly k = 2n+1−m slots | SOUND | Σ_i (2 − deg_{Q_i} v) = 2n − (m−1). |
| P2 | Thm 2.2 (Hilton, = JM Thm 5 / Cor 6) and the equivalence \|C_i\| ≥ 2r−2n−1 ⇔ p(C_i) ≤ 2n+1−r | SOUND | Matches JM pp.2–3 verbatim. Only "if" is used. |
| P3 | Thm 2.3 (Hoffman, with integrality) | SOUND | Standard statement (Schrijver Ch. 11). |
| V1 | **Lemma 5.1 (validity; the list of possible cycles)** | **SOUND** | Re-derived (§1.1). The list x C x / y C y / x C y C′ x / x C y x (i = c only) is complete. Also checked exhaustively by brute force (§3). |
| V2 | Def 5.2, Lemma 5.3 (records; split by a proper 2-edge-colouring of F*) | SOUND | Both directions re-derived (§1.2). Placing the special pair at one copy i′ is what gives (V3). |
| V3 | Demands (1), Cor 5.4, the caps δ_i ≤ κ_i | SOUND | Targets p(Q′_i) ≤ k−2 / k−3 ⇔ a_i ≥ δ_i via p(Q′_i) = p_i + 2 − a_i − [i=c]. |
| F1 | Network D, Lemma 6.2 (circulations ↔ records) | SOUND | Conservation was checked at every node type in both directions. The revised wording ("need not be one-to-one") is correct. |
| F2 | Lemma 6.3 (ψ_i(B) as a max flow, with attainment) | SOUND | Min cut recomputed explicitly (§1.3). |
| F3 | **Prop 6.4 (cut conditions (UH), (LH))** | **SOUND** | I recomputed all cut capacities (§1.3). The four (s, t)-membership cases exhaust Hoffman's conditions, and the colour sub-networks decouple. **No missing cut type.** Confirmed by full enumeration over all 2^{\|V(D)\|} node subsets on 98 small networks and every demand vector (§3). |
| U1 | Counting notation, slot identities (4) | SOUND | |
| U2 | Lemma 7.1 (bounds on u_i) | SOUND | All four claims re-derived. |
| U3 | **Prop 7.2 (UH): kE ≥ 4−2k ⇒ E ≥ −1; integrality step b = 2\|H\| + 3/2** | **SOUND** | Re-derived (§1.4). The 2\|U\| bound is indeed not used. |
| L1 | Lemma 8.1 (bounds on s_i) | SOUND | Re-derived (§1.5). In f1d0af8 the exceptional case of (c) was stated without "Δ_i = 3". That statement was true, but the proof did not show that Δ_i = 1 is impossible there (it is, because n_2 ∈ {0, 1} forces Δ_i ∈ {2, 3}). Rev. 46410cd states it correctly. |
| L2 | **Prop 8.2 (LH): case k ≤ 7; case k ≥ 8 with E ≥ −1 and the parity step** | **SOUND** | Re-derived (§1.5). The k ≤ 5 sub-case wording (kE ≥ −4 > −k fails at k = 4) is fixed in 46410cd. |
| L3 | Remark 8.3 (some bound on \|U\| is needed; the example at n = m = 3) | SOUND | Example recomputed: δ = (2, 1, 4), Σδ = 7 > 6 = 2m. The softened claim agrees with the exhaustive data I re-ran. The counting argument itself is tight in \|S\| (§3). |
| B | **Theorem B (two-vertex extension lemma)** | **SOUND** | Follows from V1–V3, F1–F3, U3, L2. |
| A1 | **§4: Theorem A from Theorem B** | **SOUND** | (k_s−2) − 2\|U_s\| = 2t−1−r for every s, so r ≤ 2t−1 is exactly the hypothesis of Thm B at every step. It is preserved automatically (§1.6). Final Hilton step: m = r+2(n−t) ≤ 2n−1. |
| A2 | Remark 3.2 (JM Thm 8 read literally is false when G may have isolated vertices) | SOUND | The counterexample (n = 3, t = 1, r = 4) is correct under the reading V(G) = V(K_r), which is the one JM's statement intends. I made that reading explicit in the text. |
| A3 | §3 (account of the gap in Claim 12) | SOUND | Agrees with the arXiv text pp.8–9 and with A4 §2.4. Not used later. |
| T1 | **Lemma 9.1 (transfer lemma)** | **SOUND** | Degree count and the "sink" argument re-derived. \|X\| ≤ 2\|I\| + \|J\| = 2\|R\|. |
| T2 | Thm 9.2 set-up: H has no isolated vertices (added in f1d0af8, and needed); r ≤ (3t−1)/2; the case r ≤ n via Liu–Chen | SOUND | The new "no isolated vertices" sentence is needed. Without it, K_1 components would enter H′ and inflate r. |
| T3 | Case r ≥ n+1: start from K_{2s+1}, size bound (9) | SOUND | 2n+s−t−1 ≥ r ⇐ r ≤ 2n−2. |
| T4 | Case 1 (n+1 ≤ r ≤ (4n−1)/3): claim, transfers, donor ranges | SOUND | f_n(n+1) = 3n−11 and f_n((4n−1)/3) = 1 re-derived. Availability 4r−4n−1 ≥ (2r−2n−2)+3 checked. |
| T5 | Case 2 (4n/3 ≤ r ≤ (3t−1)/2): claim, transfers, bookkeeping | SOUND | f_{n,t}(4n/3), 2f_{n,t}((3t−1)/2), g_n endpoints re-derived. Counts with \|X\| ≤ 2(r−n−1) checked. Donors keep ≥ 2r−2n−1. |
| T6 | Do the corrected transfers do what the counts need? | SOUND | Every transfer uses only \|X\| ≤ 2 (single-edge receiver) or \|X\| ≤ 2\|R\|. These are exactly the numbers JM's counts assume. Brute-force re-run over 93,843,621 triples: 0 failures. |
| C1 | Theorem C (Wu's conjecture) | SOUND, conditional on Hilton, Hoffman, Liu–Chen | No one in this collection has re-checked Liu–Chen. [REP] says so. |
| D1 | **Downstream: [OSC] Thm 9 (§6, p.9) "As in Javadi–Miralaei [14, Theorem 3.8 and its proof]"** | **SOUND (covered by Thm A)** | Here n_JM = k, t = k−h, sizes ≥ L / L+1, representatives may leave isolated vertices, and r ≤ 2t−1 from s ≤ 2k−1. The prescribed exterior matching is obtained by relabelling exterior vertices. |
| D2 | **Downstream: [OSC] Thm 11 (§8, p.12) "Javadi and Miralaei's matching extension [14]"** | **SOUND (covered by Thm A)** | Here r = s−2h ≤ 2t−1 is stated on p.11, and t ≥ 1. All other [14] citations in [OSC] use only the main theorem (= Thm C). |
| D3 | [OSC] citation "Theorem 3.8" | ERROR (citation), unchanged from A4 T11.6 | It should now cite [REP] Theorem A (or JM Thm 8 with r ≤ 2t−1, proved in [REP]). |
| S1 | `check_colour_lemmas.py` | SOUND; checks what is claimed | Checks Lemmas 7.1 and 8.1 as stated, for 4 ≤ k ≤ 60. It does not test the k < 8 branch "s_i ≥ min{0, k−8}"; that branch is unused. Re-run: 0 violations. |
| S2 | `check_valid_lemma.py` | SOUND; checks what is claimed | Re-run with seed 5 (the default) and 40 trials reproduces 306,446 / 12,631 exactly. |
| S3 | `test_random.py`, `test_adversarial.py`, `test_flow_large.py` | SOUND in substance; **GAP (reproducibility)**, fixed in text | All re-runs: feasible, all tests agree. Exact case counts cannot be reproduced: CP-SAT's multi-worker search is nondeterministic (same seed: 140, then 143), and the trial counts are not stated. `test_random.py` run from the command line has n ≤ 8, not n ≤ 10. |
| S4 | `test_noUbound.py` | SOUND in substance; **GAP (wording)**, fixed | The script compares CP-SAT with the flow on every case, but runs the cut check only on infeasible cases. "The three tests again agreed" overstated this. Re-run (seed 1, 200 trials): 822 cases, 156 infeasible, all with (UH) true and (LH) failing at B = ∅. |
| S5 | `pipeline.py` | SOUND; checks what is claimed | Seeds 11–14 × 40: 160/160 end-to-end decompositions verified. The figure of 436 two-vertex steps is not logged. |
| S6 | `check_thm7_counts.py` | SOUND; checks what is claimed | It checks the inequality each claim needs, not only f_n, f_{n,t}, g_n, plus availability and retention. Re-run: 93,843,621 triples, 0 violations. |
| S7 | `scripts/independent/` (internal referee) | Reproduced exactly; non-independent | (3,3), (4,4), (5,3), (5,4), (4,5) exhaustive results and the \|U\| probe all match the text. |
| X1 | Intro step (c): "the counting leaves a deficit smaller than one unit" | GAP (wording), fixed | In (UH) the counting gives only E ≥ −1, a deficit below two units. The integrality step removes E = −1. |

**Overall.** I found **no ERROR and no substantive GAP** in the new proof of Theorem B, in the deduction of Theorem A, in the transfer lemma, or in the written-out Theorem 7. The four steps the author flagged as the main points to check are all SOUND: Lemma 5.1, Prop 6.4, and the integrality and parity steps of Props 7.2 and 8.2. Together with JM's Theorem 7 counts (re-derived), this gives a complete proof of Wu's conjecture. It is conditional on Hilton's theorem, Hoffman's theorem and the Liu–Chen theorem; Liu–Chen has not been re-checked. The JM3 hypothesis issue (A4) is resolved by Theorem A. The A4 status "JM Thm 8: GAP (substantive)" can be replaced by "JM Thm 8 under r ≤ 2t−1: proved in [REP] by a different argument; Claim 12 itself is still unrepaired".

---

## 1. Line-by-line notes on the proof of Theorem B and Theorem A

### 1.1 Lemma 5.1 (validity)

- (V1) ⇔ deg_{Q′_i}(v) ≤ 2. (V2) ⇔ deg_{Q′_i}(x), deg_{Q′_i}(y) ≤ 2, counting xy when i = c.
- Given (V1) and (V2), suppose Z is a cycle of Q′_i. Every new edge zv of colour i ends at a slot (σ_i(v) ≥ 1).
  - At the end v of a nontrivial component C, σ = 1. So v carries exactly one new edge, and Z must traverse all of C to its other end w and leave by a new edge.
  - At a trivial C = {v}, Z uses the two new edges at v.
  - Hence Z alternates between {x, y} and whole components. Since x and y each occur at most once, the only possible shapes are x C x (needs d_x(C) = 2), y C y, x C y C′ x with C ≠ C′, and x C y x through xy, which exists only for i = c.
- "Joined to both" gives an x–y path through C. For nontrivial C, the x- and y-attachments must be at different ends, because σ = 1 at each end. So two such components, or one together with xy, give a cycle. The converse is therefore also correct.
- p(Q′_i) = (m+2) − \|Q_i\| − a_i − [i=c]. ✔

### 1.2 Records and the split (Lemma 5.3)

- (a) If ρ(C) = 2 then C is joined to both. For trivial C this is direct. For nontrivial C, (V3) forbids two x-attachments or two y-attachments.
- (b) Splitting:
  - F* has maximum degree 2. Each colour i ≠ c is split into i′, i″ with at most 2 edges each, and colour c has degree a_c ≤ 2.
  - F* is bipartite, so its components are paths and even cycles (a 2-cycle is a pair of parallel edges). An alternating colouring is therefore proper.
  - Each copy carries ≤ 1 x-edge and ≤ 1 y-edge, which gives (V2).
  - (V3): d_x(C) = 2 forces ρ(C) = 2 and i ≠ c. The two edges are then the special pair, which sits at one copy, so they receive different colours.
  - (V4): any component joined to both has ρ(C) = 2. A both-ends-at-u split is impossible because σ = 1 at u.
- Two components with ρ = 1 at the same copy may go one to x and one to y. This is harmless. ✔

### 1.3 The network and the cut computation (Lemma 6.3, Prop 6.4), recomputed

Fix X ⊆ V(D) and put B = X ∩ V. Lower bounds are positive only on (s, v) (value 2) and (g_i, t) (value δ_i). The colour-i part of the capacity of δ^out(X) is

cap_i(X) = Σ_{C ∉ X} σ_C(B) + Σ_{C ∈ X} ([g_i ∉ X] + [h_i ∉ X]) + [h_i ∈ X, g_i ∉ X]·(1 − [i=c]) + [g_i ∈ X, t ∉ X]·κ_i.

Arcs (v, C) with v ∉ B and C ∈ X enter X with lower bound 0 and do not matter. Different colours share only V and t, so the minimum over X ∩ D_i is taken colour by colour. With g_i ∉ X:
- If h_i ∉ X, the cheapest choice is C ∉ X whenever σ_C(B) ≤ 2. The cost is Σ_C σ_C(B) = N_i + n_2.
- If h_i ∈ X, put C ∈ X exactly when σ_C(B) ≥ 1. The cost is N_i + (1 − [i=c]).
- The minimum is N_i + min(n_2, 1 − [i=c]) = ψ_i(B).

With g_i ∈ X and t ∉ X the cost is κ_i. With g_i ∈ X and t ∈ X it is 0. The four cases are:

| s | t | Hoffman inequality, minimised over the rest of X |
|---|---|---|
| ∈ | ∉ | LHS = 0: trivial |
| ∉ | ∈ | (t, s) leaves X, u = ∞: trivial |
| ∉ | ∉ | 2\|B\| ≤ Σ_i min(κ_i, ψ_i(B)) = (UH) |
| ∈ | ∈ | Σ_{i∈I} δ_i ≤ 2\|V∖B\| + Σ_{i∈I} ψ_i(B) for every I = {i : g_i ∉ X}; strongest at I = {δ_i > ψ_i} = (LH) |

The four cases exhaust all subsets X, so **there is no missing cut type**. The [n_2 ≥ 1] bonus is exactly the h_i bypass. Removing it, or granting it to c, is caught by my brute-force test (§3, mutation tests).

### 1.4 Prop 7.2 (UH)

- The sum is Σu_i = kE, and u_i ≥ 0 for i ≠ c, while u_c ≥ 4 − 2k because f_c(B) ≤ 2p_c ≤ 2k − 2 uses p_c ≤ k − 1. So E ≥ −1.
- Suppose E = −1:
  - Then u_c = 2k − 2f_c(B) < 0, and Σ_{i≠c} u_i = 2f_c(B) − 3k ≤ k − 4.
  - So no colour i ≠ c has u_i ≥ k − 2. Every colour i ≠ c therefore either has f_i(B) = 0 (and then u_i = 0) or ψ_i ≥ 5 (and then f_i = 2k − u_i/2).
  - Summing the slot identity gives kb = 2k\|H\| + 3k/2, which is not an integer multiple of k. ✔
- My aggregation DP (§3) shows that the inequality survives the relaxation in which only per-colour profiles and Σ f_B ≡ 0 (mod k) are kept, for all 4 ≤ k ≤ 250. Allowing p_c = k breaks it: min Σu = −2k.

### 1.5 Lemma 8.1 and Prop 8.2 (LH)

- **Lemma 8.1.**
  - (a) s_i ≥ (k − n_0)(k − 4). For odd Δ, s_i ≥ (k − 4)(4 − Δ).
  - (b) s_c ≥ 2k − 4. Δ_c = 1 gives s_c ≥ 3k − 8.
  - (c), J-case: if n_0 = k − 1, then n_0 = p_i, so ψ = 0, Δ = 4 and s = −4.
  - (c), n_0 ≤ k − 2: s ≥ k − 8, using k ≥ 4 for the monotonicity in n_0.
  - (c), Δ = 1: s ≥ 3k − 16 ≥ k − 6, using k ≥ 5. Δ = 3: s = k − 8 + 2n_1.
  - Check of the exceptional case: (n_0, n_1) = (k−2, 0) with p ≤ k−1 forces n_2 ∈ {0, 1}, i.e. (p, Δ) = (k−2, 3) or (k−1, 4 − 2) = (k−1, 2). So Δ = 1 is impossible there, and the 46410cd statement "either s ≥ k−6, or Δ = 3, n_0 = k−2, n_1 = 0, s = k−8" is exact. ✔
- **Prop 8.2.**
  - k ≤ 5: S = ∅, so kE ≥ 0. k ∈ {6, 7}: kE ≥ −4 > −k.
  - k ≥ 8: kE ≥ −4j ≥ −2(k−4) > −2k, so E ≥ −1.
  - If E = −1, then ΣΔ = 2a + 1 is odd and Δ ≡ 0 on J, so some i_0 ∉ J has odd Δ and s_{i_0} ≤ 4j − k.
  - Either branch contradicts j ≤ \|S\| ≤ (k−4)/2. In the second branch the contradiction uses J ⊆ S ∖ {i_0}. ✔
- **The bound on \|U\| is tight for this proof.** In my aggregation DP, allowing ⌊(k−4)/2⌋ + 1 colours of type S makes the relaxation fail at every even k (min Σs = −k). So a better bound on \|U\| *for even k*, which Remark 8.3 now says is "probably" true, would need structural information beyond the per-colour counting. At odd k the relaxation still holds with one more S colour, i.e. with 2\|U\| ≤ k−1 (checked for all odd 5 ≤ k ≤ 99, `agg_oddcheck.py`). In Theorem A, k_s is odd exactly when r is even, and (k_s−1) − 2\|U_s\| = 2t − r. So the counting method is consistent with extending Theorem A to r = 2t. That extension would need a modified proof of Prop 8.2; I did not write one, and it is irrelevant for Wu's conjecture.

### 1.6 §4, Theorem A from Theorem B

- (I_0) is the size hypothesis. (k_s − 2) − 2\|U_s\| = 2t − 1 − r for every s, so the hypothesis of Thm B is the same condition r ≤ 2t − 1 at every stage. It is preserved trivially, and it gives k_s ≥ 4 while U_s ≠ ∅.
- The output targets are k_s − 2 = k_{s+1} on T_{s+1} = T_s ∪ {c} and k_s − 3 = k_{s+1} − 1 on U_{s+1}. This is (I_{s+1}).
- At s = n − t: m = r + 2(n−t) ≤ 2n − 1, and every p_i ≤ k, which is Hilton's condition.
- Rainbow property: G ⊆ P_1 ∪ … ∪ P_t, with one edge per class, and e_{t+j+1} = x_j y_j ∈ C_{t+j+1}. ✔
- The case t = n (no matching) is handled separately by Hilton. ✔
- Theorem A does not use G beyond the number t. So isolated vertices of G are irrelevant, as claimed.

---

## 2. Transfer lemma, Theorem 7 and the downstream use

- **Lemma 9.1.**
  - After removing X, the degrees are as follows: vertices of I have R-degree 2 and Y-degree 0; vertices of J have R-degree 1 and Y-degree ≤ 1 (in-edge only).
  - In a cycle of R ∪ Y, each maximal Y-segment is a directed subpath of an oriented D-path. Both its ends have positive R- and Y-degree, so they lie in J. Its tail has Y-out-degree 1, but vertices of J have Y-out-degree 0. Contradiction. ✔
  - The two counterexamples to JM's separation rule (Case 1 internal vertex; Case 2 two-receiver cycle z₁w₁xz₂w₂yz₁) are correct.
- **Theorem 9.2.** I re-derived every inequality listed in T2–T6 of the table and compared them with the arXiv text, pp.4–6.
  - [REP] uses \|X₂\| ≤ 2(r−n−1) and \|P_ℓ\| ≥ 3r−3n−ε. JM wrote 3r−3n−1 for the first Case 2 block, which is the ε = 1 worst case. The counts are identical.
  - The minimality used, "every graph with fewer than n edges satisfies Wu", is exactly what the r ≥ n+1 case needs, because s < t ≤ n. JM's second-level minimality (fewest vertices) is not needed once isolated vertices are removed.
- **Downstream ([OSC]).**
  - The matching-extension theorem is used only in Thm 9 (§6, p.9: "As in Javadi–Miralaei [14, Theorem 3.8 and its proof] …") and in Thm 11 (§8, p.12: "Javadi and Miralaei's matching extension [14] … Its proof starts with all r vertices, including any isolated in the representative graph … See also Theorem 3.8").
  - In both places [OSC] supplies: a decomposition of K_r into k linear forests; t seeded colours of size ≥ 2r−2k−1 and h = k − t others of size ≥ 2r−2k; one representative per seed, possibly leaving isolated vertices; r ≤ 2t − 1 (Thm 9: s ≤ 2k−1; Thm 11: r = s−2h ≤ 2t−1); t ≥ 1.
  - It needs: P_i ⊆ C_i (the whole initial colouring is preserved, wedge seeds included), and h pairwise disjoint exterior edges, one in each unseeded colour, placed on *prescribed* exterior pairs.
  - Theorem A gives exactly this with n := k. Prescribing the pairs is a relabelling of V(K_{2k+1}) ∖ V(K_r). It fits because r + 2h ≤ 2k − 1.
  - Every other [14] citation in [OSC] (pp.1, 3, 5, 9, 11, 12, 17) uses only the main theorem, which is Theorem C.
  - **Theorem A covers the downstream use, hypotheses and all.** The [OSC] citation "Theorem 3.8" should be replaced by a citation of [REP] Theorem A.

---

## 3. Computations

### 3.1 My own checks (`research/audit/A10-scripts/`; no code shared with [REP])

| Check | Scope | Result |
|---|---|---|
| `indep_cuts.py`: graph-level brute force over **all** colourings χ of the 2m new edges vs (UH)∧(LH), for **every** demand vector 0 ≤ δ_i ≤ κ_i (not only Thm B's demands) | 11 runs (m ≤ 4, n ≤ 4; m ≤ 5, n ≤ 4; m ≤ 4, n ≤ 5), random decompositions; 78,360 (instance, δ) pairs, 17,230 feasible | **0 mismatches**. Tests Lemma 5.1, Lemma 5.3, Lemma 6.2 and Prop 6.4 jointly, on both feasible and infeasible demands. Unlike [REP]'s tests, where every infeasible case had B = ∅, the cut conditions bind here at nonempty B too. In the seed-11 run, 837 of the 7,376 infeasible pairs fail *only* at B ≠ ∅, and (UH) is violated in 255 (instance, δ, B) triples (`bdist.py`). |
| same, plus Hoffman's condition over **all 2^{\|V(D)\|} node subsets** of D (≤ 19 nodes) | 98 networks (m ≤ 3, n ≤ 4), every δ | **0 mismatches**: no missing cut type |
| mutation tests of `indep_cuts.py` | ψ without bonus; bonus also at c | 725 and 79 mismatches respectively: the test has power |
| `indep_aggregate.py`: exact min-plus DP over residues mod k, relaxing to per-colour profiles + slot identity (UH: Σf_B ≡ 0; LH: Σf_A ≡ 0, one c, ≤ ⌊(k−4)/2⌋ S-colours, any number of T) | every 4 ≤ k ≤ 250 | min Σu = 0 and min Σs = 0 for all k: **the aggregation in Props 7.2/8.2 is correct** |
| mutation tests of `indep_aggregate.py` | \|S\| bound + 1; p_c ≤ k; ψ without bonus | fail at every even k / every k / every k (4 ≤ k ≤ 40) |

### 3.2 Re-runs of [REP]'s scripts (`nice -n 19`; log in `A10-scripts/reruns.txt`)

| Script | Claimed in [REP] §10 | Re-run | Checks what the text claims? |
|---|---|---|---|
| `check_colour_lemmas.py` | 0 violations, 4 ≤ k ≤ 60 | 0 violations | Yes. The unused k < 8 branch of "≥ min{0, k−8}" is not tested. |
| `check_valid_lemma.py` | 40 instances, 306,446 colourings, 12,631 valid | seed 5, 40 trials: identical; 6 more seeds agree | Yes. |
| `test_random.py` seeds 21–23 | 712 cases, n ≤ 10, all feasible, 3 tests agree | 100 trials: 143/156/129; 200 trials: 282/267/286. All feasible, 0 mismatches | Yes in substance. Counts are not reproducible (nondeterministic CP-SAT; trials unstated). The CLI fixes n ≤ 8. |
| `test_adversarial.py` seeds 31–33, n ≤ 10 | 1013 cases | 281/305/271 (100 trials), 309, 406. All feasible, 0 mismatches | Yes in substance. Same reproducibility caveat. |
| `test_flow_large.py` seed 41 | 277 cases, all feasible | 425/425 feasible (100 trials) | Yes (flow only, as stated). |
| `test_noUbound.py` | 794 cases, 187 infeasible, three tests agree, all LH at B = ∅ | seed 1, 200 trials: 822 cases, 156 infeasible, all (UH ✔, LH ✗ at B = ∅) | Mostly. The cut check runs only on infeasible cases (wording fixed). |
| `pipeline.py` seeds 11–14 | 160 instances, 436 two-vertex steps | 160/160 ok | Yes. The step count is not logged. |
| `check_thm7_counts.py` | 93,843,621 triples, 0 failures | identical | Yes. |
| `independent/*` | see [REP] §10 | all identical | Yes. |

Caveat on "three independent tests": the CP-SAT search encodes (V1)–(V4). Its *infeasibility* verdicts therefore rely on Lemma 5.1, and the flow and cut tests rely on Lemma 5.3 as well. Lemma 5.1 is checked separately, and my `indep_cuts.py` uses graph-level validity only.

---

## 4. Edits made to [REP] (textual only; no mathematics changed)

1. Intro, step (c): the "deficit smaller than one unit" wording is replaced by the accurate statement: E ≥ −1 (or E ≥ 0), with E = −1 excluded by integrality (UH) or parity (LH).
2. Remark 3.2: the reading under which the literal JM Theorem 8 fails is made explicit (V(G) = V(K_r), so the n − t matching edges must avoid V(K_r)).
3. §10:
   - a reproducibility note (CP-SAT is nondeterministic; same-seed re-runs give different case counts with the same outcome; `test_random.py` from the command line draws 3 ≤ n ≤ 8);
   - the caveat that the direct search encodes (V1)–(V4);
   - `test_noUbound.py` wording (the cut check runs on the infeasible cases);
   - seed 5 for `check_valid_lemma.py`.
4. §11:
   - "(n ≤ 10)" corrected to "(n ≤ 14)", since `test_flow_large.py` goes to n = 14;
   - pointer to this audit (new bibitem [A10]);
   - one sentence under "Use elsewhere" saying that both [OSC] uses were checked here.
5. `README.md`: "`test_noUbound.py` — that the bound 2\|U\| ≤ k−2 is needed" changed to "that some bound on \|U\| is needed", in line with the softened Remark 8.3.

I recompiled with pdflatex twice. There are no warnings and no undefined references, and the PDF is now 17 pp.

## 5. Recommendations (not done here)

- Update [OSC] p.9 and p.12 to cite [REP] Theorem A in place of "[14, Theorem 3.8 and its proof]". Then A4 rows T11.6 / JM2 / JM3 can be closed. Note that [REP] itself is unrefereed outside this collection.
- An optional strengthening that I did *not* check: if the published version of [JM] changed Claim 12, compare it with [REP]. [REP] does not depend on it.
- Liu–Chen remains an unchecked external input to Theorem C, as [REP] states.
