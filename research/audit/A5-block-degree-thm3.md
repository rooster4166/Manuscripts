# A5 — Referee audit: block-degree, Theorem 3 (block degree ≤ 7) and Theorem 2 (path absorption into an odd semi-clique)

**Target.** J. Williams, *Path absorption and Gallai's conjecture for blocks of maximum degree nine or cutwidth eight* (`gallai/01-original-manuscripts/block-degree.pdf`, 54 pp., dated Nov 24 2026). Page numbers below are the PDF's printed page numbers.

**Scope.** Everything Theorem 3 needs:

- §1 and §2: the mixed partition, the auxiliary vertex z, Lovász, the cycle-minimum properties and parity absorption.
- §3–§6: the 5-, 6-, 7- and 8-contact reductions.
- §7: Theorem 2.
- §8: the nine-cycle with three paths.
- §9: cluster restoration and the proof of Theorem 3.
- The appendix checks on pp. 52–53, as far as they are cited for these steps.

**Method.**

- I read every step line by line, together with the PDF images of pp. 8–11.
- I **independently replayed every finite computation** that Theorem 3 uses, with my own code. The two-path test is a C depth-first search, cross-checked against `tools/pathnum.py` CP-SAT. The marked-cost test is an exact dynamic program over (edge set, unused marks).
- I fetched arXiv 2611.21673 and read its §2.
- Scripts and logs are in `research/audit/A5-scripts/`. Compile `twopath.c` to `./twopath` next to `seglib.py`.

---

## 0. Bottom line

1. **No ERROR was found in the chain Theorem 2 → §2–§6 → §8 → §9 → Theorem 3.** Every step is SOUND or a minor, fixable GAP. With the replays below, Theorem 3 is **proved modulo**:
   - the classical results Lovász 1968 (path–cycle covering) and Liu–Chen (rainbow Hamilton decomposition for k ≤ 5, used only at k ≤ 3);
   - the two pair lemmas. I re-derived them exhaustively, so their *content* no longer depends on the citations.
2. **The claim "Theorem 3 does not use the large computations" is TRUE.**
   - The proof of Theorem 3 (pp. 10–12) cites only §2, §3–§5, §8 (hence §6) and Theorem 2.
   - Nothing from §10–§13 enters: no 25,003 / 1,154 (§10.2), no 36,268 (§11), no 29,077 (§12), no ≈4.86M (§13), and none of the §14 checks.
   - Theorem 3 *does* use **five moderate finite enumerations** (§4, §4 core, §5, §6 path case, §8). Their specifications are precise enough to replay, and **every count was reproduced exactly** (Table D).
3. **Citations.**
   - Path–cycle lemma. The paper cites **[17]** = Zhang–Liu–Hong, *Gallai's conjecture for 3-degenerated graphs*, Discrete Math. 347 (2024) 114057, Lemmas 2.5–2.6. **arXiv 2611.21673 is the paper's [16]**, ZLH's *K5-minor-free* paper, and its own Lemmas 2.5–2.6 are unrelated statements. The task brief conflated the two. [16] does restate "[3, Lemmas 2.5–2.6]" (its [3] is the paper's [17]), and the restatement matches the block-degree usage word for word:
     - a path and a cycle meeting in 1–5 vertices are absorbable, except K5 − e with possibly empty pendant paths at the ends of the missing edge;
     - two cycles meeting in 1–**4** vertices are absorbable.
   - Two cycles meeting in exactly 5 vertices: the paper attributes this to Chu–Fan–Liu [8]. I could not access [8] (ScienceDirect returned 403), so that *citation form* is **UNCLEAR**. Its content is verified exhaustively below.
   - Javadi–Miralaei [11] is needed in Theorem 3 only at k ≤ 3. That range is covered by Liu–Chen [2] (n ≤ 5), by my K3/K5/K7 replay, and by audit A4 (k ≤ 7).

---

## D. Dependency list: computations used by Theorem 3

| # | Where | What | Claimed | Spec replayable? | Independent replay (A5) |
|---|---|---|---|---|---|
| D1 | §4, p. 5 | Contact orders, h = 6 (D6 × reversal; also cyclic shift for a second cycle) | 38 path, 12 cycle | Yes | **38 / 12** ✔ |
| D2 | §4, p. 5 | Inclusion-minimal admissible subdivision sets, h = 6 | 254 + 240 = **494**, all two-path decomposable | Yes. One reading point: "two different segments" means two distinct segment indices, and the two members of one parallel class count. With this reading the count is exact. | **254 / 240, 0 failures.** Also all 46,258 path and 25,640 cycle admissible sets, minimal or not: 0 failures. |
| D3 | §4, p. 5 | Core-only six-vertex instances (C6 plus a Hamilton chord path, and the octahedron); marked inequality for all nonempty S | 4 path orders + 1 cycle order, 63 mark sets each | Yes | **4 / 1** (30 and 3 labelled), 315 checks, **0 violations** |
| D4 | §5, p. 6 | Templates, h = 7 | 192 path, 39 cycle | Yes | **192 / 39** ✔ |
| D5 | §5, p. 6 | Minimal admissible sets, h = 7 | **1,348 + 989**, all decomposable | Yes | **1,348 / 989, 0 failures.** Also all 936,206 + 357,332 admissible sets: 0 failures. |
| D6 | §6, p. 7 | Eight-contact **path** classification. Used by Theorem 3 only through §8. | 1,320 templates; 137 failing unsubdivided; exactly one other failing order, 03476125; 27 subdivision sets | Yes | **1,320; 137 (all fail); unique order (0,3,4,7,6,1,2,5) with classes 12, 34, 67; all 27 pair-only sets fail; all 243 sets with one extra non-pair segment succeed** ✔ |
| D7 | §6, p. 7 | Eight-contact **cycle** classification. *Not used by Theorem 3.* | 202 templates; 403 failing labelled sets, all of size ≤ 1 | Yes | **202; the 403 admissible sets of size ≤ 1 all fail; 5,172 minimal sets of size ≥ 2 all succeed** ✔ |
| D8 | §8, pp. 9–10 (`verify_nine.py`) | Three omitted-site-0 orders; choice counts over the 7 triple classes; orbits; compulsory chords; replacement rows | Orders 25618347, 27634185, 41856327; counts (0,0,0,0,0,0,4); orbits of size 3 and 9; ∅ versus {03, 25} | Yes | **All reproduced.** The 12 labelled configurations split into orbits of 3 and 9. Orbit 2 repeats compulsory chords (my representative shows 25 and 47; the paper's shows 03 and 25 — same orbit). The three rows partition the 23 labelled links, are simple on the core, carry A's variable links only on row 1 and B's only on rows 2–3, and keep ends 0,5 / 2,4 / 4,6. ✔ |
| D9 | §3, p. 4 | K5 (paths acb, abdec, beadc) and K5 − ab (adc, cebd, bcaed) mark tables | Hand proof | n/a | Hand-checked. The marked inequality also holds for all 31 mark sets of each graph (exact DP). ✔ |
| D10 | Thm 2 (§7, p. 8); used in §9 | Rainbow Hamilton decomposition: any k edges of K_{2k+1} lie on distinct cycles | [11] (general k) | n/a | **k = 1, 2, 3: all 1 + 2 + 5 edge-set types realised** ✔. This also follows from Liu–Chen [2] for n ≤ 5. |
| D11 | §3, p. 4 (external) | Path–cycle and cycle–cycle pairs with ≤ 5 contacts | [17] Lemmas 2.5–2.6; [8] | n/a | **Exhaustive over all labelled orders and all subdivision patterns, h = 2..5.** <br>Path case: the only failures are h = 5, unsubdivided, P a Hamilton path of the complementary 5-cycle (10 labelled orders), i.e. K5 − ab plus tails. <br>Cycle case: the only failures are h = 5 with the second cycle the complementary 5-cycle and at most one subdivided segment (2 + 20 labelled), i.e. K5 and K5 with one edge replaced by a path. Nothing fails at h ≤ 4. ✔ |

**Not in Theorem 3's dependency set:**

- §10.2: 25,003 and 1,154; §11: 36,268; §12: 29,077; §13: ≈4.86M.
- §14: 4,477; 311,352; 7,481; 50,352.
- p. 53: the appendix templates (260 for K3/K5/K5−; 1,691 → 314 for the K7 family). Theorem 3 uses Theorem 2, which is proved in the text; see F5 for why the K7-family check could not replace it anyway.

**Model used for every two-member replay.** This is the paper's own model; its exactness was re-proved for this audit.

- Common vertices 0..h−1. C is the cyclic order; the partner has a linear or cyclic order.
- Each segment is either direct or subdivided by one vertex. Simplicity means at most one direct segment per parallel class.
- Exactness holds in both directions:
  - subdividing an edge preserves a two-path partition;
  - contracting an interior edge of a long segment maps a two-path partition to one of the shorter segment, the only degenerate case being when the union is itself a cycle.

  So "subdivided once" is equivalent to "subdivided arbitrarily".
- Trimming the tails is valid because the two trimmed ends are odd and lie on different output paths.

**Checker validation.**

- My C two-path checker agreed with `pathnum.solve(budget=2)` on 1,300 random connected graphs (865 yes, 435 no). It also agrees with CP-SAT on all 8 minimal sets of the exceptional order (all INFEASIBLE).
- Caveat: a first version of my checker had a connectivity bug (path + disjoint cycle accepted). It was caught by the CP-SAT cross-check on order E and fixed, and all runs above were repeated with the fixed binary.

**Conclusion-level checks of (A).**

- The marked inequality q(F,S) ≤ ⌊(n − |S|)/2⌋ holds for **every connected graph on ≤ 6 vertices and every nonempty S**, with 0 violations. This covers n = 4, 5, 6, i.e. 6 + 21 + 112 graphs, which includes all block-degree ≤ 7 graphs of these orders.
- n = 7: partial, see the addendum at the end.
- (B) for n ≤ 7 was already done in `research/replay-plan.md` (no failures).

---

## V. Verdict table

| Id | Step (page) | Verdict | Note |
|---|---|---|---|
| **§2** | | | |
| V2.1 | X = F + z; cost identity 2λ_m = \|S\| + 2q_m; Lovász at odd \|X\|; leaf trick at even \|X\| (p. 2) | SOUND | A simple path has ≤ 1 end at z, so every z-ended path contains exactly one spoke and the identity is exact. The leaf trick gives cost ≤ n/2 − 1/2. |
| V2.2 | Property 1: marks on a residual cycle are used in every maximum assignment (p. 3) | SOUND | The split keeps the cost and removes a cycle. |
| V2.3 | Property 2: a path end on C uses both C-neighbours (p. 3) | SOUND | All three mark cases are checked. Not used by Theorem 3. |
| V2.4 | Absorption preserves an assigned start, by parity (p. 3) | SOUND | Both ends of P are odd in P ∪ C. Sanity run: 76 decomposable P ∪ C with tails, all two-path partitions enumerated, 0 violations. |
| **§3** | | | |
| V3.1 | Restoration lemma for Z with prescribed attachments, cases 1–3 (pp. 3–4) | SOUND | Case 2 arithmetic: r − z ≤ ⌊(h − z + f)/2⌋ when z + f ≥ 1 or h is even. Case 3 even-component and triangle-bridge saving: re-derived. The triangle-bridge graph has order 2a + 4 < n. Note that h ≥ 4 already suffices. |
| V3.2 | The two five-intersection pair lemmas (p. 4) | Content SOUND (D11). Citation **UNCLEAR** for [8]; [17] consistent via [16] | See F1 and F2. "A path of arbitrary length" should read "length ≥ 2" (F6). |
| V3.3 | Reduction to residual cycles of length ≤ 5; a nonabsorbable pair contains a 5-cycle (p. 4) | SOUND | A path uses ≤ 4 core edges of a 5-set, so C has 5 core edges. In the cycle case the unsubstituted cycle is the 5-cycle. |
| V3.4 | F connected; a partner-less cycle is a component; ≤ 1 partner (4 + 4 > 5 chords) (p. 4) | SOUND | |
| V3.5 | C ∪ D = K5: paths acb, abdec, beadc (p. 4) | SOUND | Partition checked; endpoint triangle abc; marked bound for all 31 mark sets. |
| V3.6 | K5 − ab: paths adc, cebd, bcaed and the mark table (p. 4) | SOUND | Endpoint path a–c–d–b. Assignments 1, 2, 2, 3, 3 checked; also all 31 mark sets by DP. |
| V3.7 | Marks with attachments; three a–b rows; restoration at h = 5 (p. 4) | SOUND | z ≤ 1; coincident exterior ends handled. |
| **§4** | | | |
| V4.1 | Segment model, trimming, monotonicity (p. 5) | SOUND | Only "decomposable trimmed ⇒ absorbable" is needed, and it holds. |
| V4.2 | Six-contact finite lemma (p. 5) | SOUND | Replayed (D1, D2). |
| V4.3 | Residual 6-cycle: ≥ 5 of 9 chords per partner; ≤ 1 partner; core structure (p. 5) | SOUND | |
| V4.4 | Core-only instances (p. 5) | SOUND | Replayed (D3). |
| V4.5 | Three a–b rows; restoration at h = 6 (p. 5) | SOUND | |
| **§5** | | | |
| V5.1 | Exposing two ends at x in an odd tight component (p. 6) | SOUND | |
| V5.2 | Seven-contact finite lemma (p. 6) | SOUND | Replayed (D4, D5). |
| V5.3 | ≥ 6 of 14 chords per partner, so r ≤ 2; rows; z ≤ r (p. 6) | SOUND | |
| V5.4 | Local partition into ≤ 4 rows with dedicated attachments (p. 6) | SOUND | Every combination checked: 1–2 path rows; a core Hamilton cycle with a path row (the 2-edge path's far end avoids the port, since D has no edge to the port along C); two internal cycles (contradicts Property 1). |
| V5.5 | Z = V(F): cost 4 − z ≤ ⌊(7 − z)/2⌋ (pp. 6–7) | SOUND | |
| **§6** | | | |
| V6.1 | Path classification at 8 contacts (p. 7) | SOUND | Replayed (D6). |
| V6.2 | Cycle classification at 8 contacts (p. 7) | SOUND | Replayed (D7). Not used by Theorem 3. |
| V6.3 | Endpoint-parity characterisation (p. 7) | SOUND (method only) | My replay does not use it. |
| **§7 (Theorem 2)** | | | |
| V7.1 | Lower bound k + 1 (p. 8) | SOUND | |
| V7.2 | Case a ≤ r: filled core J′, greedy R, rainbow opening, the two-slot rule (p. 8) | SOUND given rainbow | δ(J′) ≥ 2k − m + f exceeds the current length. The endpoint pairs of the R-rows form a cycle on V(R). The forbidden-row rule prevents exactly the cycle closure. |
| V7.3 | Case a > r: selected prefixes; label swapping in runs; H-row for isolated gaps (p. 8) | SOUND given rainbow | Row-end usage checked: each end of an H-row is adjacent to only one other gap, so there is no conflict. |
| V7.4 | Case r = 1, all gaps available (p. 8) | SOUND | Both rows are simple, the edge accounting is exact, and both ends are exposed. |
| V7.5 | Rainbow theorem [11] in "any k edges" form (p. 8) | SOUND for k ≤ 3 (D10; Liu–Chen [2]). General form: see A4 | |
| V7.6 | Appendix check "seven-vertex exterior components at maximum degree seven" (p. 53) | GAP (non-load-bearing) | See F5. |
| **§8** | | | |
| V8.1 | ≤ 2 internal visits per site; each path has exactly 6 internal visits and 8 contacts; omitted sites and extremities partition V(C); tails leave the block at once (p. 9) | SOUND at block degree ≤ 7. GAP in the statement | See F3: the degree hypothesis is not stated in §8. |
| V8.2 | Each path must be the exceptional order with the gap doubled; the three orders; end pairs (p. 9) | SOUND | Uses V6.1; replayed (D8). |
| V8.3 | Counts (0,0,0,0,0,0,4); the "3³" triples; orbits of 3 and 9 (p. 9) | SOUND | Replayed. The text extraction shows "33"; the PDF reads 3³. |
| V8.4 | Orbit 2 impossible (repeated compulsory chords); orbit 1 has none (p. 9) | SOUND | Replayed. |
| V8.5 | Replacement rows for C, A, B; tails; assignments; cost (pp. 9–10) | SOUND | Replayed. Each row carries the variable links of one partner only, and tails of one partner only. The "two tails cannot meet" remark is not even needed. |
| **§9 (Theorem 3)** | | | |
| V9.1 | Induction order; connected reduction; class closure (p. 10) | SOUND | |
| V9.2 | Eight-contact threshold for (A) from §3–§5 (p. 10) | SOUND | |
| V9.3 | A path member exists; a cycle–path adjacency exists (p. 10) | SOUND | |
| V9.4 | Cluster deletion: m + a − b ≥ h; cost g = p + 2q + 2 − a − 1_{q>0}; Σ ≤ g + ⌊(t − m + b)/2⌋; target met when h ≥ 4 + 2p + 4q − 2·1_{q>0} (pp. 10–11) | SOUND | Re-derived: the target holds iff 2g ≤ h − a, which is implied since a ≥ 0. Σ(n_i − \|S_i\|) = t − m + b is checked. The arithmetic is not shown in the paper (minor). |
| V9.5 | Theorem 2 absorbs markless odd-semi-clique components, keeping assignments (pp. 10–11) | SOUND | A current row always meets J, shares no edge with it, and later absorptions keep the cover. |
| V9.6 | Edges of B stay in B; h ≥ 3p + 4q (p. 11) | SOUND | Ear argument. 2h ≥ 6p + 8q from ≤ 2 internal visits per site. |
| V9.7 | Case table (q ≥ 1, p ≥ 2), (q = 0), (1,1), (1, ≥ 3) (p. 11) | SOUND | Each inequality re-derived. For (1, ≥ 3): g = p − a + 2q gives the target 2 + 4q ≤ 3 + 4q. In the non-meeting case h ≥ 8q ≥ 4 + 4q. |
| V9.8 | p = 1, q = 2, h = 11: the u′uvv′ path; four rows (p. 11) | SOUND | u′ ≠ v and v′ ≠ u by edge-disjointness; u′ ≠ v′ by choice. |
| V9.9 | p = 3, q = 0, h = 9 → §8 (p. 11) | SOUND | |
| V9.10 | (B) at even order from (A) with a singleton (p. 11) | SOUND | |
| V9.11 | (B) threshold: a partner-less cycle; lengths 5, 6, 7; no-exterior cores K5, K5−, a 7-core with 1 partner (≤ 3 paths), a 7-core with 2 partners (≥ 19 edges, so a semi-clique) (pp. 11–12) | SOUND | |
| V9.12 | (B) exterior: ⌈h/2⌉ + ⌊(n − h − f)/2⌋ ≤ ⌊n/2⌋ for h = 5, 6, 7 with f ≥ 1 (p. 12) | SOUND | |
| V9.13 | (B) all-cycles: exactly k cycles; one block; 8k > 7(2k + 1)/2 for k ≥ 4 (p. 12) | SOUND | |

---

## F. Findings

**F1. Citation identity (UNCLEAR → resolved for [17]; p. 4 and bibliography p. 54).**

- The brief attributes "Lemmas 2.5–2.6" to arXiv 2611.21673. In the paper, 2611.21673 is reference **[16]** (ZLH, K5-minor-free, submitted 2026-11-14). Its own Lemma 2.5 ("a vertex of degree ≤ 2 forces all others ≥ 5") and Lemma 2.6 (a K5-minor-free edge addition) have nothing to do with path–cycle absorption.
- The block-degree paper correctly cites **[17]** (Discrete Math. 347 (2024) 114057) for Lemmas 2.5–2.6.
- [16] §2.2 restates [17]'s two lemmas. The path–cycle form, with exception K5 − e plus possibly empty pendant paths, is **exactly** the form used on p. 4. The two-cycle form there stops at **four** common vertices.
- So the five-vertex two-cycle statement rests on Chu–Fan–Liu [8] alone. I could not open [8] (ScienceDirect returned 403), so its exact published form is **UNCLEAR**. This includes whether [8] states it unconditionally or under its Δ ≤ 6 hypotheses.
- **Impact on Theorem 3: none.** D11 proves both statements exhaustively in an exact finite model.
- *Fix:* replace the dependency on [8] by the finite lemma (h ≤ 5, about 49k labelled cases), or quote [8]'s lemma number and hypotheses.

**F2. "Two standard absorption results in their five-intersection forms" (GAP, wording; p. 4).**

- The cycle exception "K5 with exactly one edge replaced by a path of arbitrary length" should say *length ≥ 2*.
- My enumeration confirms that the second cycle may carry the substituted path on any one of its 5 segments, or on any of C's. Exactly one segment of the pair is subdivided (20 labelled cases).
- The paper's derivation ("the other is a five-cycle") is correct.

**F3. §8 does not state its degree hypothesis (GAP, presentation; p. 9).**

- "Three would require six edges in addition to the two of C" is a contradiction only when Δ(B) ≤ 7. Likewise "the seven required incidences … any further tail immediately leaves it" needs Δ(B) ≤ 7.
- At block degree 8 both statements fail as justifications: three internal visits fit in 2 + 6 = 8.
- Theorem 3 invokes §8 only at block degree ≤ 7, so Theorem 3 is unaffected.
- *Fix:* add "in a block of maximum degree at most seven" to the first sentence of §8. Separately, check that §10–§12 do not cite §8 at degree 8 (outside this audit).

**F4. Verifier code is absent; the specifications are adequate (GAP, reproducibility; pp. 5–7, 10).**

- `verify_six.py`, `classify_intersections.py`, `classify_eight.cpp`, `derive_orders.cpp` and `verify_nine.py` are not in the collection.
- The textual specifications nevertheless determine the enumerations uniquely, up to one reading point: "two different segments" must allow both members of one parallel class.
- Every claimed count was reproduced exactly (Table D). Replay plan item R1 is now **done**, and in addition D2/D5 were extended to all admissible sets, not only the minimal ones.

**F5. The appendix's degree-7 check of Theorem 2 for 7-vertex components is not a substitute for the general proof (GAP, non-load-bearing; p. 53).**

- The appendix discards templates with Δ(J ∪ P) > 7. In §9, however, the current row P may pass through a vertex v ∈ J with deg_J(v) = 6, using one edge inside J's block and one edge in another block (v a cut vertex of F). Then Δ(J ∪ P) = 8, while every block still has degree ≤ 7.
- So the 1,691-template check does not cover every use of Theorem 2 in Theorem 3. The general proof on pp. 7–8 does, and needs only the rainbow theorem at k ≤ 3. That is Liu–Chen [2] and my D10.
- *Fix:* say that the appendix check is supplementary, or drop the Δ ≤ 7 filter (the templates stay finite).

**F6. Minor and textual (all SOUND in substance).**

- Section 3 states h ≥ 5 for the restoration lemma; h ≥ 4 suffices for the triangle-bridge order argument.
- The arithmetic behind "this meets the target whenever h ≥ …" (p. 11) is omitted: target ⟺ 2g ≤ h − a.
- "Each entry checks at most 33" is a text-extraction artefact for 3³.
- The paper says "independent replay", but no code or certificates are in the collection. The same holds for all of D1–D8.

No step was found to be false as stated.

---

## R. Recommended fixes, in order of importance

1. **Cite or replace [8].** Either quote the exact lemma and hypotheses of Chu–Fan–Liu for two cycles with five common vertices, or include the finite h ≤ 5 lemma, whose segment-model proof is ≤ 1 page plus the enumeration replayed here.
2. Add the block-degree ≤ 7 hypothesis to §8 (F3).
3. Make clear that Theorem 2 at k ≤ 3 needs only Liu–Chen [2] (n ≤ 5). This removes Javadi–Miralaei from the dependency chain of Theorem 3 entirely.
4. Ship the verifiers, or point to this replay (`research/audit/A5-scripts/`).
5. Wording fixes in F2 and F6.

---

## Replay files (`research/audit/A5-scripts/`)

| File | Contents |
|---|---|
| `twopath.c` | Exact "≤ 2 paths" decision by DFS over first paths, with a complement-is-one-path test. |
| `seglib.py` | Segment model, orbit enumeration, minimal admissible sets. |
| `replay_678.py` → `out_678.txt` | D1, D2, D4, D5 (minimal sets). |
| `replay_small.py` → `out_small.txt` | D11 (h = 2..5, all labelled), plus all admissible sets at h = 6, 7. |
| `replay_eight_path.py` → `out_eight.txt` | D6. |
| `replay_eight_cycle.py` → `out_eight_cycle.txt` | D7. |
| `check_E.py` | CP-SAT confirmation of order E. |
| `replay_nine.py` → `out_nine.txt` | D8. |
| `core_checks.py` (with `marked.py`) → `out_core.txt` | D3 and D9. |
| `rainbow.py` → `out_rainbow.txt` | D10. |
| `concl_A2.py` (with `marked2.py`) | (A) for all S on connected graphs with n ≤ 7. |
| `ends_check.py` | V2.4 sanity check. |
| `thm2_test.py`, `thm2_test_inc.py` → `out_thm2.txt` | Random CP-SAT tests of Theorem 2 for J ∈ {K3, K5, K5−e, K7, K7−e, K7−2e}. |
| `thm2_explicit.py` | Explicit Theorem 2 construction on a K7 instance. |
| `out_A7.txt` | Partial n = 7 run of the (A) check. |

## Addendum: final status of the long-running checks

- **(A) at n = 7.** All nonempty S were checked on the first 600 of the 853 connected 7-vertex graphs (every graph in `data/conn7.g6` up to that point; ≤ 16 edges): **0 violations**. I stopped the run on the remaining denser graphs because the machine was overloaded (load average ≈ 45). The pure-Python dynamic program is too slow there. This is a conclusion-level supplement, not a proof dependency.
- **Theorem 2, random tests.**
  - K3: 13 instances. K5 and K5−e: 27 instances. Each was checked with CP-SAT for a partition into k + 1 paths having both ends of P as ends, and verified edge by edge: **all pass**.
  - K7 family: the first instance (J = K7, P = 1–100–6) returned UNKNOWN, a 120 s CP-SAT timeout under load. It is not a failure. `thm2_explicit.py` builds the partition by following the paper's own proof (case a ≤ r): R = 1–6–0–2, a rainbow decomposition at {16, 60, 02}, the gap halves on R and on the 16-row, and ends reserved at 1 and 6. It obtains 4 valid paths with ends at 1 and 6.
  - I stopped the remaining K7 instances for the same load reason. Theorem 2 at k ≤ 3 rests on the line-by-line audit (V7.1–V7.4) together with D10.
