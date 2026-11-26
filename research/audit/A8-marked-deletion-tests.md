# Audit A8: marked-reduction, deletion tests at d = 4, 6, 8 (MR pp. 129–150)

**Paper.** `gallai/01-original-manuscripts/marked-reduction.pdf`. Printed page = PDF page.

**Scope.**

- The p. 129 deletion-degree paragraph ("The neighborhood of the deleted vertex") and its two examples.
- The book theorem and the K_i seven-site table (pp. 130–131). The two-degree-two construction and the odd-order root-contact construction (pp. 131–132).
- §21 in full: exceptional shapes; Lemma 121; Thms 122–124; Cor 125; Lemmas 126–127; Thm 128; Cor 129; Thm 130; Lemma 131; Thm 132; Lemma 133; Prop 134; Thms 135–137; Cor 138.

**Method.**

1. Adversarial line-by-line reading. Every Fan transfer inequality was checked by hand.
2. Machine checks of every finite table printed in the text.
3. An **independent replay of Thm 124's seven-site certificate**: new search code, plus a second, independent Python verifier of the exported certificate.
4. Independent re-derivation of the two other certificates the text only describes: the K_i table and Lemma 133's `boundary-even.json`.
5. Conclusion-level exhaustive and random checks with a new exact path-number solver. The solver was cross-validated against `tools/pathnum.py`.

Scripts and outputs are in `research/audit/A8-scripts/` (§8).

## 0. Overall verdict

**No ERROR found.** Every CLAIMED roadmap node in scope is sound, given the external results listed in §4:

- T(4);
- T(6)-ii;
- T(8)-ii;
- T(6)-i at d_B(r) ∈ {2, 4};
- T(8)-i at d_B(r) = 2.

**Thm 124's finite fact replays exactly from the text.**

- Every count that is an invariant of the statement is reproduced: 1,044; 271; 44/57/672; 810/870/14,112; 15,792; 15,407/345/40.
- The count 10,906 and the |D| histogram are not invariants. They depend on the authors' labelled representatives and on their choice of route L, so they cannot be reproduced from the text. My certificate has 13,482 distinct G, and all of them have |D| ≤ 5.

**Remaining issues.** None of them is a logical gap in the MR text. All are dependency or reproducibility items:

- (U1) FHZ is genuinely needed for **two** seven-site shapes in Thm 124's structural branch. Botler–Sambinelli (BS) does not cover them, and neither does the certificate.
- (U2) Lemma 126 rests on the unquoted Chu–Fan–Zhou star lemma [8, Lemma 2.1].
- (U3) Thms 135 and 137 rest on supplement tables with 9,330 and 235 cases. These tables are not in the text, so the two theorems cannot be replayed.
- (G1, G2) Presentation and supplement availability.

**Botler–Sambinelli suffices at d = 4.** It also replaces FHZ at every use on at most 5 even sites. Lemma 133 removes the Shaik dependency flagged in A2-F2.

## 1. Verdict table

| # | Item | Page | Verdict |
|---|---|---|---|
| 1 | Reduction of both rooted tests to the ordinary ceiling on the bridge/diamond doubles, whose E-subgraph is exactly 2K, K = J[N(z)−r] | 129 | SOUND. The parities were rechecked. The identities 2F₂−1 and 2F₃−1 are from Thm 59 (audited, A1). |
| 2 | **T(4)**: both tests at d = 4 | 129 | **SOUND.** FHZ applies: its abstract wording ("G_e contains no triangle pair and each block of G_e has max degree ≤ 3", JORSC 2023) matches the MR paraphrase. **BS alone suffices**: \|K\| = 3, so 2K has Δ ≤ 2 and is not a single triangle; BS Thm 13 (Δ(EV) ≤ 3 ⇒ Gallai graph or SET) then gives even the floor. Fan 2005 alone does not suffice when K is a triangle. |
| 3 | "At d = 6 a failure requires two universal vertices in K" | 129 | SOUND, and Shaik is not needed. Thm 123 settles test (ii) at d = 6 outright. For test (i), Lemma 133 (replayed, §3.5) gives the ≤ 1-universal case. A2-F2 can be closed by citing Lemma 133. |
| 4 | Examples: K6−{02,23,13}; the 9-vertex host | 129 | SOUND (machine-verified: partitions, 3-connectivity, unique even vertex 7, universal sites 6 and 8, terminal neighbours 3, 6, 8, four paths with two ends at 1 after deletion). |
| 5 | Book theorem (W odd, even sites induce K2∨K3, some odd vertex misses them ⇒ floor) | 130 | SOUND. All six cases were hand-checked step by step (parities and every Fan inequality); the case split is exhaustive. Independently, a certificate exists for all 31 A (§3.4). |
| 6 | Book ⇒ both deletion tests at d = 6 (one or two private leaves, trimming) | 130–131 | SOUND. |
| 7 | K_i table (31/30/27/15 covered; uncovered abe; abd, abcd, abde, abcde; \|A\| ≥ 3) | 131 | **SOUND: reproduced exactly** (§3.4). The uncovered sets stay uncovered up to \|D\| ≤ 8, so the table is sharp for this method. |
| 8 | Two degree-two vertices on a common even adjacent pair | 131 | SOUND. |
| 9 | Odd-order deletion with root contacts t = 1…5 (two universals) | 131–132 | SOUND. Every donor inequality was hand-checked, e.g. t = 1: 3 > 0, 2 > 1, 3 > 2, then 1 > 0; t = 5: 5 > 0, 4 > 1, 3 > 2. |
| 10 | "Seven exceptional graphs" K0–K3, M, P, C | 137–138 | SOUND. Exactly 7 of the 34 five-vertex graphs are exceptional. On ≤ 5 vertices, "nonexceptional" ⇔ "in BS's class 𝒢" (or a subgraph of a 𝒢-member), checked exhaustively. |
| 11 | Lemma 121 and its 24-row table | 138 | SOUND. All rows verified: L is a simple p–q path; the deleted edges are disjoint and outside L; z is the unique even site; both receivers see no zero site; the donors are positive; the receivers are distinct. The rows cover all 10 pairs up to Aut for every shape. |
| 12 | Thm 122 | 138–139 | SOUND. The nonexceptional branch needs only BS (by item 10); leaves are never SET-compatible. |
| 13 | Thm 123 (T(6)-ii) | 139–140 | **SOUND.** The 5-row M table is verified, including "a recipient lies in {b, c}" and coverage under b↔c, d↔e. The t = 2 and t = 3 contact conditions were machine-checked on all 7 shapes; the only t = 2 failures are M with contacts bc or de, exactly as stated. |
| 14 | **Thm 124** (≤ 9 even vertices, two marks exposed) | 140–141 | **SOUND.** The finite fact was replayed independently (§2). The deduction from the fact (arms, lists, A, Pyber, Fan 3.3) was rechecked; every hypothesis matches Fan's Lemma 3.3 verbatim. The structural branch needs FHZ for 2 classes (U1). |
| 15 | Cor 125 (F₀ ≤ 7 sites + trees) | 141 | SOUND. Padding isolates can never lie in Y; tree components are non-adjacent to F₀, stay forests under arm deletion, and are in BS/FHZ class. |
| 16 | Lemma 126 (odd-root star) | 141–142 | SOUND modulo **U2**. The BS Thm 13 / SET exclusion was checked (r odd ⇒ r has no even neighbour; r even ⇒ isolated in EV; r isolated ⇒ even-order component). The count k−j+(j+1) and the parity argument were checked. Conclusion verified on 846,755 instances at n = 9. |
| 17 | Lemma 127 | 142 | SOUND. The truncation and rerouting argument was checked, including the case where a Menger path starts at r. |
| 18 | **Thm 128** (T(8)-ii) | 142 | **SOUND** given Thm 124 (replayed), Lemma 126 (U2), Lemma 121 and Thm 122. The case split t ≥ 3 / t ≤ 1 / t = 2 is exhaustive. In the t ≤ 1 branch, r has ≤ 1 T-neighbour, so 2 > 1 holds for restoring rs. |
| 19 | **Cor 129** (d_B(r) = 2, ≤ 6 even) | 142–143 | **SOUND.** BS suffices in the nonexceptional branch. In the exceptional branch the distinct rows at u, v exist because each has 2 ends on 2 distinct rows (Hall). |
| 20 | **Thm 130** (8 even, d_B(r) = 2) | 143–144 | **SOUND.** Cases (a)–(c) are exhaustive. The 35-entry segment/forest table was verified. The "seven-even exposure" sub-claim and the (c) star branch (via Lemma 126) were checked. |
| 21 | Lemma 131 and the degree-ten remarks | 144 | SOUND. Not load-bearing; covers only t = 1, 2 and ≥ 5 at d = 10. |
| 22 | Thm 132 (route through an even K, Δ(K) ≤ 4) | 144–145 | SOUND. The SET exclusion (2(m−3) > 3) and the inward/outward restoration counts ((s+1)/2 in; then ≥ 3 ends before each outward step; final 2) were checked. The C_m² construction was verified for all odd m ≤ 61 and all j. |
| 23 | **Lemma 133** (≤ 1 universal site) | 145–146 | **SOUND.** `boundary-even.json` is absent, but the finite fact (93 contact sets) was re-derived independently (§3.5). The path-restoration step along a shortest r–T path was checked. |
| 24 | Prop 134 (any degree-2 vertex) | 146 | SOUND. Only K1's page e has degree ≤ 2 in its shape. All three R-paths were checked; the residual even sites induce forests. |
| 25 | Thm 135 (cubic vertex) | 146–148 | **UNCLEAR (U3).** The endpoint construction (ht towards h, Q restored outward) is SOUND. The three-fan case analysis depends on a 9,330-entry table that the text does not contain. |
| 26 | **Thm 136** (d_B(r) = 4) | 148–149 | **SOUND.** All t = 0,…,4 were checked, including the SET sub-case (P = a,d,s or a,s) and both ab-toggle sub-cases in t = 0. |
| 27 | Thm 137 (a T-site of degree 4) | 149–150 | **UNCLEAR (U3).** The complete-T example is verified. The 235 local cases are not in the text. |
| 28 | Cor 138 | 150 | Inherits U3 from Thms 135 and 137. Not used by any CLAIMED node. |

## 2. Replay of Theorem 124's seven-site certificate

### 2.1 The exact finite statement (FS124)

Let X = {0,…,6}. For every graph F on X, either (S) or (C) holds.

**(S) Structural.**

- F contains no two triangles sharing exactly one vertex, and
- every block of F has maximum degree ≤ 3.

**(C) Certified.** There is Y ⊆ X with |Y| ∈ {5, 6, 7} such that the following holds. For every unordered pair {p, q} ⊆ Y and every A ∈ 𝒜(F, Y, p, q), there are:

- a simple p–q path L in F[Y], and
- an edge set D ⊆ E(G) with |D| ≤ 5, where G := F − A − E(L),

such that, with b₀(x) := deg_D(x) mod 2:

1. (G − D)[{x : b₀(x) = 0}] is a forest;
2. WIN(D, b₀) holds.

**The admissible arm-edge sets 𝒜(F, Y, p, q).**

- Take two disjoint sequences (x₁…x_a) and (y₁…y_b) of distinct elements of X∖Y, each possibly empty.
- The candidate edges are the consecutive pairs of (p, x₁, …, x_a) and of (q, y₁, …, y_b) that lie in E(F).
- 𝒜 consists of all subsets of these candidate edges, taken over all such pairs of sequences.

**The game WIN.**

- WIN(∅, b) is true.
- For M ≠ ∅, WIN(M, b) holds iff there are a receiver w and a nonempty set S ⊆ {t : wt ∈ M, b(t) > 0} with
  Σ_{t∈S} b(t) > |{x : wx ∈ E(G)∖M, b(x) = 0}|,
  such that WIN(M∖{wt}, b + e_w − e_t) holds **for every** t ∈ S.

This is exactly the text's two-item fact. "Every branch ends with all of D restored" is the M = ∅ leaf. The game is precisely the hypothesis of Fan's Lemma 3.3. I checked Fan's Lemmas 3.3 and 3.4 verbatim from JCTB 93 (2005), pp. 120–121: if Σ D(xᵢ) > |{v ∈ N_H(a) : D(v) = 0}| with H = G∖{ax₁…ax_s}, then some ax is addible, with all other counts unchanged.

**The deduction from FS124 to Thm 124 is sound.** I rechecked each of the following:

- Arms stop at their first Y-site, so A ∩ E(F[Y]) = ∅ and R is simple.
- Every F-edge on an arm joins listed-consecutive sites.
- The even vertices of H − E(R) − D are exactly the zero sites in X. The exterior vertices, u and h are all odd.
- Pyber gives the floor (BS Thm 2(b)), applied componentwise: ≤ k − 1 paths.
- b is a lower bound, so the RHS over-counts actual zero neighbours.

### 2.2 Implementation and results

The implementation is `A8-scripts/seven.c` (search) and `export.c` (certificate export with explicit restoration trees).

- The rule is: largest Y first, lexicographic among subsets; routes L longest first; D by increasing size.
- Running time is under 1 s.

| Quantity | Paper | Replay |
|---|---|---|
| isomorphism classes on 7 sites | 1,044 | 1,044 (atlas). Σ 7!/\|Aut\| = 2²¹ was checked independently. |
| structural (S) | 271 | 271. Recomputed independently by brute force over 2-connected induced subgraphs with a vertex of degree ≥ 4. |
| representatives with \|Y\| = 5 / 6 / 7 | 44 / 57 / 672 | **44 / 57 / 672** |
| (p, q, A) choices for \|Y\| = 5 / 6 / 7 | 810 / 870 / 14,112 | **810 / 870 / 14,112** (total 15,792) |
| A empty / one edge / two edges | 15,407 / 345 / 40 | **15,407 / 345 / 40** |
| failures among the 773 non-structural classes | 0 | **0** (max \|D\| = 5) |
| distinct labelled G | 10,906 | 13,482 (longest-L), 14,056 (shortest-L), 13,801 (DFS order) |
| \|D\| histogram 0..5 | 2415, 3539, 3740, 1068, 135, 9 | 3550, 4855, 3874, 1072, 125, 6 (minimal \|D\| per G) |

**Independent second check.** `verify124.py` shares no code with the C search. It re-reads the exported certificate (`cert124.txt`, 16,836 lines) and checks:

- the orbit sum;
- the structural flags;
- that every admissible (p, q, A) is present, with 𝒜 re-enumerated from the list definition in Python;
- that L is a simple p–q path in F[Y] and that G = F − A − E(L);
- that D ⊆ E(G) and |D| ≤ 5;
- the forest condition;
- every node inequality and every child of every tree.

Result: **0 bad**.

**What the text does not determine.** It does not fix the labelled representatives or the choice of L, so the 10,906 count and the |D| histogram are not reproducible. They are not invariants of FS124. The Y-sizes and the (p, q, A) counts are reproduced exactly, so the authors evidently also chose the largest admissible Y. The (p, q, A) count depends only on which sites lie outside Y, and for |Y| < 7 these are essentially forced (isolated or poorly attached sites).

### 2.3 Robustness: which external theorem the structural branch needs

Of the 271 structural classes:

- 266 lie in BS's class 𝒢 (Botler–Sambinelli, JGT 2021, Thm 5).
- 1 more (8 edges, `mask 1282313`: triangles 014 and 356 joined through the degree-4 vertex 4) is a **subgraph** of a 𝒢-member, obtained by adding edge 05. So BS covers it.
- 2 more (`1280323`, `1079693`) have seven-site certificates, so they need neither BS nor FHZ.
- **2 classes need FHZ.** These are `1073613`, a diamond {0,1,3,4} with bridge 12 to triangle 256, and `1106381`, the same with K4 in place of the diamond.
  - They are not subgraphs of any 𝒢-member. Any block containing both a diamond/K4 triangle and triangle 256 contains the edge 12, which gives vertex 1 block-degree ≥ 4.
  - They have no certificate with |D| ≤ 8.
  - FHZ's hypothesis holds for both: there is no triangle pair, and the blocks are subcubic.

**Consequence.** T(8)-ii (Thm 128), Thm 130(a) and Cor 125 depend on FHZ only when the 7 even sites induce one of these two shapes. FHZ's published abstract states exactly the paraphrased hypothesis; A7 should confirm the full statement.

The other 56 structural classes (≈ 21%) have no certificate at all, e.g. because they have ≥ 3 isolated sites. They are all in 𝒢 directly.

## 3. Other finite tables and certificates

### 3.1 Lemma 121, the Thm 123 M rows, and the Thm 130 segment table

These are verified by `tables.py`:

- Lemma 121: 24/24 rows correct; every shape covers all 10 pairs under Aut, with |Aut| = 12, 4, 12, 120, 8, 2, 8 for K0, K1, K2, K3, M, P, C.
- Thm 123: the 5 M rows are correct and cover all pairs under b↔c, d↔e.
- Thm 130: the 35 segment entries are all paths, and each leaves a forest after deleting its terminal vertex.

### 3.2 The exceptional shapes and BS

On ≤ 5 vertices, "exceptional" (a block of max degree 4, or a triangle pair) holds for exactly 7 of the 34 graphs. Exceptional ⇔ not in BS's 𝒢 closure (`small5.py`). Hence every MR use of the "marked FHZ consequence" with ≤ 5 unmarked even sites can cite BS Thm 5 instead. The added leaves are odd with no even neighbour, so no SET exception arises. These uses are Thm 122, Thm 123, Cor 129, Lemma 133, Thm 130(b, c) and Thm 136.

### 3.3 Contact conditions in Thm 123

The t = 2 condition ("one contact has two neighbours in T outside the contacts") and the t = 3 condition (non-contacts adjacent, or joined through a contacted universal site) were checked on all 7 shapes and all contact sets. The only t = 2 failures are M with contacts bc or de, which the M table handles.

### 3.4 The K_i seven-site table (p. 131) and the book

`local.c` searches the p. 131 game:

- the sites are K_i ∪ {u, v}, with edge uv, N(u) ∩ K_i = A and N(v) ∩ K_i = ∅;
- D is chosen so that exactly one site is even;
- b is 0 there and 1 elsewhere;
- the leaf condition is M = ∅.

| Shape | Paper: covered / uncovered | Replay |
|---|---|---|
| K0 | 31 / none | **31 / none** (minimal \|D\| 3–6) |
| K1 | 30 / abe | **30 / abe** |
| K2 | 27 / abd, abcd, abde, abcde | **27 / identical** |
| K3 | 15 / \|A\| ≥ 3 | **15 / identical 16 sets** |

The uncovered sets remain uncovered with |D| ≤ 8. The explicit book proof (six cases) was also hand-verified inequality by inequality; it uses up to |D| = 6.

### 3.5 Lemma 133's boundary table (`boundary-even.json`, absent from the collection)

The game is:

- T ∈ {M, P, C}, together with y and N(y) ∩ T = N ≠ ∅;
- D leaves 0 or 2 even sites;
- with 2, a designated site p must have a retained edge, and gets b = 2, b(p′) = 0, b = 1 elsewhere;
- the leaves require b(y) ≥ 2.

Result: **93/93 covered**: M 31, P 31, C 31, with minimal |D| ≤ 4. The paper's "109 leaves" figure is tree-specific and not reproducible.

## 4. External dependencies

| Result | Where used | Status found here |
|---|---|---|
| Fan 2005, Lemmas 3.3 and 3.4 | everywhere | **Checked verbatim** (copy in the scratchpad). The MR paraphrase is exact, including "all other counts unchanged" (Def. 3.2(c)). |
| Pyber (E-subgraph a forest ⇒ ⌊n/2⌋) | Thms 124, 130, Prop 134 | Floor version confirmed via BS Thm 2(b). |
| Lovász (≤ 1 even vertex ⇒ ⌊n/2⌋ paths, componentwise) | passim | classical |
| Botler–Sambinelli, JGT 97 (2021) (arXiv 1911.04546): Thm 5 (𝒢-closure ⇒ Gallai graph or SET); Thm 13 (Δ(EV) ≤ 3 ⇒ Gallai graph or SET) | Lemma 126, Thm 132, Thm 136(t=3) | Statements checked from arXiv. **Sufficient at d = 4 and for every ≤ 5-site use.** |
| Fan–Hou–Zhou, JORSC 11 (2023) | p. 129; Thm 124 structural | The abstract matches the paraphrase. **Needed only for the 2 seven-site classes of §2.3.** |
| Chu–Fan–Zhou [8, Lemma 2.1] (star lemma) | Lemma 126 → Thms 128, 130(c) | **Not quoted; not checked** (U2). The paper is not on arXiv. The same lemma is used in §§ ≤ 114. |
| Shaik [25] | p. 129 two-universal remark | **Not needed**: superseded by Lemma 133 (test i) and Thm 123 (test ii). |

## 5. Conclusion-level checks

**Solver.** `pn.h` is a C exact-cover search over paths with memo and a budget, used as an exact test p(G) ≤ budget. Endpoint requirements are encoded with private leaves. The equivalences used are:

- F₂(B, r) = p(B + leaf_r) for an even r of positive degree;
- F₃(B, r) = p(B + 2 leaves at r) for an odd r of degree ≥ 3;
- F₂,₂(H; u, h) = p(H + leaf_u + leaf_h).

These equivalences were proved in the audit notes (trim leaf, split if a singleton vanishes).

**Cross-validation against `tools/pathnum.py` (CP-SAT).**

- Path numbers of all 965 connected graphs on 6 and 7 vertices: 0 mismatches.
- 358 endpoint-constrained instances, comparing min_ends against the leaf form: 0 mismatches.

**Graph generation.** `gen9.c` extends `conn8.g6` and removes isomorphic duplicates by refinement plus a canonical permutation search. It produces **194,066** 2-connected 9-vertex graphs, matching OEIS A002218.

| Check | Population | Instances | Fails |
|---|---|---|---|
| test (i), \|J\| = 5, 7, 9, exhaustive (B = J − z from conn4/6/8, J 3-connected, unique even z) | 1 + 28 + 5,231 J | at \|J\| = 9: d = 4: 13,000; d = 6: 10,914; d = 8: 1,296 | 0 |
| test (i), \|J\| = 11, random | 8,485 J | 58,926 (d = 4, 6, 8, 10; all d_B(r)) | 0 |
| test (i), d = 6, targeted at the open shape (two universals in K, δ(B) ≥ 5, even degrees ≥ 6) | \|J\| = 11: 17,234; \|J\| = 13: 2,380 | 103,404 + 14,280 | 0 |
| test (ii), \|J\| = 6, 8 exhaustive | conn5, conn7 | 10 + 1,124 | 0 |
| test (ii), **\|J\| = 10 exhaustive** (all 2-connected 9-vertex B) | 194,066 B | **771,972** (d = 4, 6, 8; d_B(r) = 3, 5, 7) | 0 |
| test (ii), \|J\| = 12, random | — | 17,521 | 0 |
| Thm 124 conclusion, \|H\| = 9, 9 even vertices (all pairs u, h) | 1,648 H | 59,328 | 0 |
| Thm 122 conclusion, \|H\| = 5, 7 | — | 3,031 | 0 |
| Thm 128 conclusion, \|B\| = 9, 7 even, all odd r of degree ≥ 3 | 32,745 B | 65,490 | 0 |
| Lemma 126 conclusion, \|B\| = 7 (connected, r non-cut) and \|B\| = 9 (2-connected) | — | 846,755 at n = 9 | 0 |
| Even rooted test on all 7,123 2-connected 8-vertex B (covers Cor 129, Thm 130, Thm 136, Lemma 133, Prop 134 at n = 8) | 7,123 | 29,460 | 0 |

These checks exercise the statements, not the proofs. They are consistent with every claimed result and, as expected, give no evidence about open cases.

## 6. Findings

**U1. UNCLEAR (external), Thm 124 p. 140, structural branch; inherited by Cor 125 and Thms 128, 130(a).**

- FHZ is needed for two seven-site shapes: diamond or K4, bridged to a triangle (§2.3).
- BS does not cover them, and the certificate fails up to |D| ≤ 8.
- **Fix.** Quote FHZ's theorem; A7 is verifying it. Alternatively, handle the two shapes by a direct argument and cite BS everywhere else. With BS alone, T(8)-ii is open exactly for these two J[N(z)−r] shapes.

**U2. UNCLEAR (external), Lemma 126 p. 142.**

- The CFZ star lemma [8, Lemma 2.1] is used in paraphrase. The paraphrase is: "spokes to ends restore at constant count into paths and cycles, cycles through r, ≤ ⌊|A|/2⌋".
- The conclusion was verified on 846,755 instances at n = 9.
- **Fix.** Quote [8, Lemma 2.1] verbatim, including how paths through r are handled.

**U3. UNCLEAR (unavailable supplement), Thms 135 and 137, pp. 147–150.**

- The 9,330-entry and 235-case tables are not printed and cannot be rebuilt from the prose without re-deriving the case structure.
- Not load-bearing for any CLAIMED node.
- **Fix.** Ship `verify_cubic_cross.py`, the local-case data and an independent replay, or print the tables.

**G1. GAP (presentation), Thm 124 p. 141.**

- The figures "10,906 distinct labelled graphs" and the |D| histogram depend on unstated representative labellings and route choices.
- **Fix.** State that they are properties of the supplied certificate, or list the representatives. The invariant counts are fine.

**G2. GAP (availability), pp. 141, 146.**

- `verify_seven_core.py`, `boundary-even.json` and its Lean proof are absent from the collection.
- The text does suffice to rebuild them; this was done here (`A8-scripts/cert124.txt` is a full independent certificate).
- **Fix.** Add them, or reference this replay.

**Citation fixes (not defects).**

- p. 129: cite BS Thm 13 for T(4).
- Use BS for all ≤ 5-site marked bounds.
- p. 129: replace "requires two universal vertices … by Shaik" with "by Lemma 133".

## 7. Roadmap implications

| Node | Proposed status |
|---|---|
| T(4) | **AUDITED** (A8). Botler–Sambinelli suffices; FHZ is not needed. |
| T(6)-ii | **AUDITED** (A8). BS suffices. |
| T(8)-ii | **AUDITED modulo FHZ (2 shapes) and CFZ Lemma 2.1.** comp: Thm 124 certificate independently replayed; test (ii) exhaustive at \|J\| ≤ 10. |
| T(6)-i, d_B(r) ∈ {2, 4} | **AUDITED** (Cor 129, Thm 136, Lemma 133 certificate replayed). Depends on BS only. |
| T(8)-i, d_B(r) = 2 | **AUDITED modulo FHZ (2 shapes) and CFZ** (Thm 130). |
| A2-F2 (Shaik at d = 6) | Can be closed: Lemma 133 gives the two-universal reduction. |

## 8. Reproduction

All files are in `research/audit/A8-scripts/`. Run them from that directory. Requirements: gcc, Python 3, networkx, and OR-Tools for the cross-checks.

| Purpose | Command(s) |
|---|---|
| Seven-site graphs and flags | `python3 gen7.py` → `g7.txt` |
| Thm 124 replay | `gcc -O2 seven.c -o seven && ./seven 5 1` (summary at the end). `seven2.c` takes arguments `DMAX SKIP ORDER`: SKIP 2 also certifies structural graphs outside 𝒢; ORDER varies the L order. |
| Certificate export and independent check | `gcc -O2 export.c -o export && ./export && python3 verify124.py cert124.txt` |
| Tables, shapes, examples | `python3 tables.py; python3 misc.py; python3 small5.py; python3 examples.py` |
| K_i and Lemma 133 certificates | `gcc -O2 local.c -o local && ./local 8` |
| Path solver and conclusion checks | `pn.h`, `chk.c` (modes `testi`, `testii`, `t124`, `t128`, `l126`, `beven`), `gen9.c` (`./gen9 < conn8.g6 > bic9.g6`, ~1 min), `sampler.c`, `target.py`; outputs `*.out` |
| Solver cross-validation | `pntest.c` + `xval.py`; `xval2.c` + `xval2.py` |
