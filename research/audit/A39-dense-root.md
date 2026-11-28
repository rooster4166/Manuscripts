# A39: Audit of dense-root (manuscript, `DenseRoot.lean`, scripts, data)

Date: 2026-11-28. Referee stance: adversarial. Grades: **SOUND**; **ERROR** (false as stated); **GAP** (missing argument, missing provenance, or an omission that changes how a result reads; fixable); **NIT** (wording).

**Version.** I audited commit **d443852**: `dense-root.tex` (486 lines, md5 `036ce387…`), `DenseRoot.lean` (1,083 lines, md5 `55a8e869…`), the scripts, and the working-tree `data/`.

Three commits landed during the audit:
- **73bd190** and **33fc1f0** add `DenseRootB.lean` and rewrite the Lean status of Theorem B in the abstract, the Results table, Remark 4.3, §8 and Files. They change nothing else in the manuscript.
- **e473506** is another session's snapshot of some of my scripts. I committed nothing.

Per the brief, `DenseRootB.lean` and the new Lean claims for Theorem B are **not audited**. My paper-level checks of Theorem B stand either way. `DenseRoot.lean` is unchanged.

**Numbering.** "l." is a line of `dense-root.tex` at d443852. Statements are numbered as in the PDF: Lemma 1.1, Definition 2.1, **Lemma 2.2** (families), Theorem 2.3, Theorem A = 3.1, Corollary 3.2, Theorem B = 4.1, Corollary 4.2, Remarks 4.3–4.4. The brief, the README and the `DenseRoot.lean` docstrings call the family lemma "Lemma 2.1" (F14).

**Auditor files** (`research/audit/A39-scripts/`; scratch outputs in the session scratchpad, not committed):
- `runs.sh`: every command I ran.
- `g6.py`: my own graph6 parser.
- `indep_cov.py`: an independent recount of the Theorem A/B conditions and of the hypotheses of MR Thms 47/50/74/166. It shares no code with `thm_cov.py`, and it enumerates connectors generically: every path of length 1 or 2 with both ends in N that makes N odd, without using T or Z.
- `literal_AB.py`: runs the proofs of Theorems A and B literally. It enumerates every Lovász decomposition, applies the paper's attachment rules with every tie-break, checks each claim of the attachment and counting steps, and then runs the Hall matching and the Lemma 2.2 reassembly, checking the output from scratch.
- `verify_drm.py`: checks `drm -v` witnesses from scratch. Φ must pair the even vertices, D0 must be Lovász, and it rebuilds a family by its own search and checks the decomposition of B.
- `verify_ret.py`: checks the shipped `ret.c` witnesses from scratch.
- `two_connectors.py`: the counterexample for F4.
- `frozen_exception.py`: Test1 at the one frozen root where the method fails.
- `misc_checks.py`: 3-connectivity, triangle data, distances, MR Prop 139 / Thm 140 hypotheses, frozen recount, residual witnesses.
- `axioms.lean`, `nonvacuous.lean`: Lean checks.

---

## 0. Verdict

1. **The mathematics is correct.**
   - I checked every proof line by hand: Lemma 1.1, Lemma 2.2, Theorem 2.3, Theorem A, Corollary 3.2, Theorem B (paper only at d443852) and Corollary 4.2. I found no false step.
   - **Order 9.** I ran Theorems A and B literally at all 1,756 roots: 494 Theorem A roots and 2,822 connectors at 1,262 roots. That is 918,222 Lovász decompositions and 2.32 M attachment plans, all tie-breaks included.
   - **Random graphs, k = 5, 6, 7.** The same literal run covers 1,148 Theorem A instances and 4,227 connector instances, with t up to 6 (§3).
   - **What was checked.** Every claim of the Theorem B case analysis held in every case:
     - no trivial member lies on Q;
     - exactly one L-path has its far end at q_Q;
     - at most δ trivial members are unpaired;
     - the pairs are disjoint, lie in N ∖ V(Q), and have the heavier vertex as attachment;
     - every trivial member has an own path;
     - the λ bound holds;
     - both upper bounds on |J_S| hold for **every** S, whether or not the degree condition holds.
   - Every Hall-feasible plan reassembled into k paths of B with exactly two ends at r: **0 violations**.
2. **The Lean is faithful.**
   - `DenseRoot.lean` compiles. All six headline theorems depend only on `propext`, `Classical.choice` and `Quot.sound`. There is no `sorry`, `admit`, `native_decide` or `axiom` in the library.
   - The hypotheses match the text, including the role of ε (a parameter ≥ the paper's indicator, which is harmless because the condition is monotone in ε) and the J-form.
   - The hypotheses are satisfiable (a C₄ instance compiles).
   - Small description gaps: F10.
3. **Every count in Table 1, §5 and §7 reproduces with my own code.** Two descriptive sentences in §5 are wrong (F5, F6).
   - These include 1,756 / 494 / 1,262; Theorem A 459 (404 unscheduled); Theorem B 838 (δ = 0) and 1,143 (1,041); A ∪ B 1,602 (1,445); MR 74 / 166 24 / 111; 123 with any MR hypothesis; A ∪ B ∪ MR 1,658 (1,501); method 1,756; every-D 1,742 / 481; the 154 = 52 + 102 split with the h₇ profile; residual roots 42 / 18 / 24 / 4; `ret.c` 39 / 17 / 24 / 4 with 3 + 1 UNK; frozen 113 = 23 + 90 with 112 successes.
   - **Test1 at all 1,756 is now independently constructive.** All 1,756 `drm -G -v` witnesses and all 1,756 shipped `ret.c` witnesses pass my from-scratch checkers. So do the 84 residual `ret.c` witnesses and the 112 frozen witnesses.
4. **Findings.**
   - **F1 (GAP).** The comparison with the collection omits **MR Proposition 139**. Its hypotheses hold at **all 1,756** order-9 roots, so as read the unrefereed collection already claims Test1 there. The "+56" framing understates this.
   - **F2 (ERROR).** "A variant with **one** free path succeeds at 112 of 113." With one free path the method succeeds at **105**; 112 needs two free paths at the degree-3 roots.
   - **F3 (ERROR).** "Frozen roots … are not an obstruction for the method": it fails at one of them. The Hamiltonian explanation covers 15 of 60 Φ-systems.
   - **F4 (ERROR).** §8: "the proof of Theorem B extends verbatim" to several connectors. It does not; I give an explicit instance.
   - **F5 (ERROR).** "52 roots … at distance 3": three are at distance 4.
   - **F6 (ERROR).** "The exact witnesses of `ret.c` have 8 nontrivial members": the counts are 6–10.
   - **F7 (GAP).** Provenance: every `data/*.out` file is git-ignored, the residual `drm` runs exist only in `/tmp`, and the recorded commands do not match.
   - **F8–F14 (NIT).** Wording.

**Recommendation.** Minor revision. No theorem is wrong. Fix F1–F7; F1 changes how §5 and §6 should be read at order 9.

---

## 1. Graded items

### §1 Setting, Lemma 1.1

| Item | Grade | Notes |
|---|---|---|
| Lemma 1.1(a) | SOUND | r lies on (d(r) + e(r))/2 = k − 1 + e(r)/2 paths, since a path has distinct ends. So e(r) = 2 and all k paths pass through r. The text's "at least e(r) + (d − e)/2" is in fact an equality. |
| 1.1(b) | SOUND | d_G(x) ≡ [x ∈ Z] (mod 2) for x ∈ N, and d_G(s) ≡ 1 − [s ∈ Z]. The count \|N ∖ Z\| + [s ∈ Z] = \|T\| − 1 + 2[s ∈ Z] is right. |
| 1.1(c) | SOUND | \|T\| = 2k − d(z) is even. The cases "≤ 1" and "exactly 3" are right. It counts all even vertices (degree 0 included); Theorem A says "positive even". In the 3-connected setting the two coincide. |
| 494 / 1,262 | SOUND | Recomputed. |

### §2 Families and Hall

| Item | Grade | Notes |
|---|---|---|
| Lemma 2.2, forward | SOUND | M_x x r y M_y is a path because paired members are disjoint and avoid r. The edges rx are used once each, and e(r) = \|U\|. |
| Lemma 2.2, converse | SOUND | Cut the k paths at r: 2(k − 2) + 2 = 2k − 2 = \|N\| members. Not in Lean (F10). |
| Theorem 2.3 | SOUND | Γ(S) = C ∖ J_S, so Hall with defect two ⇔ t + \|J_S\| ≤ k + 1. For t ≤ 2 this is trivial because \|C\| = k − 1. The u = 1 and u = 2 cases give k − 2 pairs and 2 singletons. Lean `hallReassemble` follows this exactly, including unmatching one edge. |

### §3 Theorem A, Corollary 3.2

| Item | Grade | Notes |
|---|---|---|
| Lovász step | SOUND | s is odd iff g exists, so Σe = 2k − 2 and there are k − 1 paths. |
| Attachments | SOUND | At most one end is s, and ends are distinct. Trivial members = {g} ∪ (far ends in N), k − 1 of them. |
| Pair bound (u ≥ 1) | SOUND | g is not an end, and the pairs are disjoint. |
| First and second alternatives | SOUND | 2\|J_S\| ≤ h_t − [d(g) ≥ 2t] + 2[g ∈ J_S] ≤ h_t + ε. Own paths are distinct, and g has no own path. |
| "Every Lovász decomposition gives one" | SOUND (paper) | The Lean statement is existential (F10). |
| Cor 3.2(a) | SOUND | Eulerian B: N is odd in G, s is even, ε = 0, d_B(x) ≥ 2 automatically. This is re-tight Thm 3.1 with the hypothesis weakened. |
| Cor 3.2(b) | SOUND in the 3-connected setting; NIT | It needs d_B(g) ≥ 2, i.e. d_J(g) ≥ 3, for the unique g ∈ N ∖ Z. The Setting paragraph does not assume 3-connectivity (F11). At n = 9 the "≤ 4 of six have degree 7" form is an iff, since t = 3 only. |

### §4 Theorem B (paper only at d443852), Corollary 4.2

| Item | Grade | Notes |
|---|---|---|
| Lovász step | SOUND | All of N is odd in G' and \|V(G')∖{r}\| = 2k − 1, so s is even. The L-paths pair up N. |
| Case δ = 0, P(q₁) = P(q₂) | SOUND | Far end of that path = q₁ = q_Q. The other k − 2 L-paths have both ends in N ∖ V(Q). |
| Case δ = 0, a ≠ b | SOUND | a, b ∉ {q₁, q₂}, and a ≠ b because ends are unique. b is trivial with partner a, d(a) ≥ d(b). The far end of P(q₁) is q₁ = q_Q. |
| Case δ = 1, o(y) = q₂ | SOUND | P(q₁) ≠ P(y), and o(q₁) ∉ V(Q) is the one unpaired trivial member. |
| Case δ = 1, o(y) ∉ {q₁, q₂} | SOUND | o(q_i) ≠ y and a, b ≠ o(y). o(y) is unpaired, and the δ = 0 analysis applies to q₁, q₂. |
| "Exactly one L-path has its far end at q_Q"; injectivity | SOUND | q_Q is an end of exactly one L-path and is not its attachment. Attachments: k − 1 + 1, trivial members k − 2. |
| "At most δ unpaired; pairs disjoint inside N ∖ V(Q)" | SOUND | Checked by hand, and literally on all cases (§3). |
| λ bound | SOUND | A vertex v lies on ⌈d_G'(v)/2⌉ L-paths: (d + 1)/2 for v ∈ N, d/2 for s. The union bound applies, and Q ∈ J_S ⇒ t ≤ λ. |
| Both bounds; "in the second bound every trivial member has an own path" | SOUND | Every trivial member is the far end of exactly one L-path (all of N are ends), so the own-path argument also covers the unpaired one. Own paths are distinct. |
| Statement hygiene | NIT | The theorem does not state \|B\| = 2k (it is used: s is unique), while Theorem A does. "d_B(x) ≥ 2" is redundant, since N is odd in G' (F11). |
| Cor 4.2 | SOUND | The connector condition is automatic (q₁, q₂ even in G; the middle vertex is s or in N ∩ Z). The n = 9 "fails only if h̃₃ = 4 and λ ≥ 3" is correct: only t = 3 occurs and the second alternative is impossible. |
| Remark 4.4 (why not lift) | NIT | "the open DL(1)": dl-one shows DL(1) *fails* at universal twins and is open otherwise. |

### §5 Computation

| Item | Grade | Notes |
|---|---|---|
| `ret.c` decides the family form without assuming B Eulerian | SOUND | I re-derived every pruning rule (lower bound, capacity, end capacity with the d_R-parity futures, dead members) for general B. All 1,756 + 84 YES witnesses verify from scratch. |
| `drm.cpp` description | SOUND | The Lovász search is complete: start at the least unused odd vertex. The leaf requires every odd vertex to be an end and the matching is exact. |
| Table 1, all rows | SOUND | Recomputed independently and identical to `coverage.py`, `cov1597.py`, `look.py` and `crosscheck.py` (0 mismatches). Blank cells: A ∪ B with s ∉ Z = 459, MR on unscheduled = 119 (NIT). |
| Caption: six roots need `-G`; 1,750 without it | SOUND | Shipped `drm9.out` = the run *without* `-G` (6 NO). `-G` gives 1,756 (F7). The six are 4 + 2 roots of `Hqzn^~}` and `Hqz~v~}`, each with seven vertices of degree 7. My verifier independently rejects all 1,920 and 2,816 Lovász decompositions at two of them (Φ = ∅). |
| "1,597 unscheduled … those among them with triangle data" | SOUND; NIT | 10,118 roots have data; 1,597 of the 1,756 degree-7 roots have data, and these are exactly the unscheduled ones. "Triangle data" is never defined here. |
| 154 = 52 + 102 | SOUND, except F5 | 52 roots have no connector (50 with h₇ ≤ 2). 102 roots fail the condition (36 / 17 + 29 / 14 + 6). |
| Residual families | SOUND numbers; F6, F7 | 42 / 18 / 24 / 4 roots; d(z) = 6; 7, 9 or 11 even vertices; `ret.c` 39 / 17 / 24 / 4 with 3 + 1 UNK at 2·10⁷. `drm` gives 88 UNK, in `/tmp/claude-0/dr` only. |
| "Lovász paths long enough that a trivial member lies on almost every one" | NIT | No data is given for this. |

### §6 The collection

| Item | Grade | Notes |
|---|---|---|
| Test1 ⇔ q(B,{r}) ≤ k − 1 | SOUND | MR §2.1 defines q(G,S) = min_P(\|P\| − ρ_P(S)). An r-end forces two (d_B(r) is even), and k − 1 paths split at an interior visit. |
| ⇔ p(B + leaf at r) ≤ k | SOUND; NIT | Trim or extend the leaf. MR Thm 114 states Test1 itself; the leaf ("leafy") form is Thm 144's / Thm 170's. |
| Thm 4 | SOUND reading | J = K_{2k+1} − H, \|E(H)\| ≤ k + 1, marked bound on J. Neither B nor B + leaf has this form. |
| Thms 12, 13, 78; SP 14.1, 14.2, 14.5, 14.8 | SOUND reading | All are "sufficiently large". SP 14.1 with b(r) = 2 and the obvious profile gives Test1 at every root when δ(B) ≥ (1/2 + ε)\|B\|. Cor 14.2 also gives it, and Thm 78 (n = 2k, d(x) even) gives it directly. |
| Thm 47 | SOUND reading | Universal in B ⇔ outside N(z) with d_J = n − 2. b_r = 2 is admissible. 0 roots. |
| Thm 50 | SOUND reading; NIT | It needs k ≥ 8. The c = 2 alternative also requires \|E(G[X])\| ≤ ⌊k²/4⌋ − k − 2. 0 roots. |
| Thm 74 | SOUND reading and route | r has degree 1 in D; orient its path component from r. 24 roots. |
| Thm 166 | SOUND reading and route | Vertices of B-degree ≥ 2k − 2 ⇔ d_J = n − 2. Σ b_y = u ≥ \|X ∩ T\| forces u ≥ \|T\|/2. My exact budget check agrees with `mr166`: 111 roots. |
| Cor 168, Thm 170 | SOUND reading | Eulerian B ⇔ cone. |
| "at the 123 roots … `ret.c` confirms" | SOUND | 123 = MR any. |
| Completeness of the list | **GAP (F1)** | MR Prop 139 (and the Cor 138 / Thm 144 bound) is missing. |
| "No theorem … in the collection applies" to the residual families | SOUND as far as checked; NIT | Besides the table, I checked Cor 138's list (Prop 134, Thms 135–137: degrees ≤ 4), Prop 139 (d_B(r) = 6) and Thm 140 (an odd vertex of degree 5 with ≥ 3 neighbours in T). None applies: δ(B) ≥ 6, even vertices have degree ≥ 6, d_B(r) ∈ {12, 14}. The paper should say which theorems were checked (F12). |
| The collection is unrefereed and only "hypotheses hold" is claimed | SOUND | l. 389, 419–421. |

### §7 Frozen roots

| Item | Grade | Notes |
|---|---|---|
| 113 = 23 + 90 (min_phi = 5, degree < n − 2) | SOUND | Recount matches `frozen9.txt` and multi-token's table, whose definition is "Φ never drops". |
| The family count with free members | SOUND | Cut at r. Paths avoiding r are the free members. |
| 112 / 113 (all 90 of degree 5; 22 of 23 of degree 3) | SOUND | Rerun, and all 112 witnesses verify from scratch. |
| "one free path" (abstract, Results table) | **ERROR (F2)** | |
| Exception `Huv]z~}` r = 2, G = K₇, "exhaustive … at most 60 per g, paths of length ≤ 6" | SOUND | In K₇ the Φ-systems are exactly 15 matchings × (1 + 3 one-edge detours through g) = 60 per g, and K₇ has no odd vertex for `-G`. So the cap is exhaustive. NO is reproduced with `-C 60 -L 6`. The shipped file was made with L = 3 (F7). |
| "Every Lovász path of K₇ minus a 3-matching is Hamiltonian, so the method has no room" | NIT (F3) | True only for the 15 matching systems: 18 edges in 3 paths of ≤ 6 edges. The other 45 systems leave 17 edges. |
| "not an obstruction for the Lovász-plus-matching method" | **ERROR (F3)** | |
| Residual frozen roots 27 / 7 / 6 undecided | SOUND numbers; NIT | Outputs are in `/tmp` only. The clt graph's 2 frozen roots are omitted (F13). |

### §8 What remains

| Item | Grade | Notes |
|---|---|---|
| m connectors (m − 1 when s ∈ T) | SOUND | |
| "The proof of Theorem B extends verbatim with one term [λ_j ≥ t] and one unpaired trivial member per connector" | **ERROR (F4)** | |

### Lean (`DenseRoot.lean`)

| Item | Grade | Notes |
|---|---|---|
| Build, axioms | SOUND | `lake env lean GallaiLean/DenseRoot.lean` compiles: 9 s, only deprecation and linter warnings. `#print axioms` for `famReassemble`, `hall_defect_two`, `hallReassemble`, `exists_decomp_of_oneEven`, `test1At_of_decomp` and `test1At_of_oneEven` gives [propext, Classical.choice, Quot.sound]. A grep finds no `sorry`, `admit`, `native_decide` or top-level `axiom` in `lean/GallaiLean/`. `GallaiLean.lean` imports the file. I did not re-run `lake build`: another session was editing `DenseRootB.lean`, so the 18,434-job count is not re-verified. |
| Definitions | SOUND | `Test1At J z r` = ∀ hr, ∃ D : PathDecomp (J − z), size ≤ (\|V\| − 1)/2 ∧ 2 ≤ ends r. `starDel` = B − r with r isolated, and `evenSet` excludes degree 0, so `hev` is exactly "≤ 1 vertex of positive even degree". `heavyNbrs` uses d_B. `delVert` = induced J − z. |
| `famReassemble` | SOUND | Lemma 2.2, forward direction: lists of pairs and singletons, Nodup, covering N, pairs compatible; conclusion size = \|pr\| + \|sg\|, ends r = \|sg\|. |
| `hall_defect_two`, `hallReassemble` | SOUND | Theorem 2.3 exactly: #A + 1 = k, d(r) + 2 = 2k, C-members pairwise disjoint, Hall for \|S\| ≥ 3. |
| `exists_decomp_of_oneEven` | SOUND | The hypotheses are those of Theorem A. ε enters as a parameter with `hε` (ε ≥ 1 if some neighbour of r is even in G); since `hstar` gets harder as ε grows, the paper's ε is the strongest instance. The attachment rule in the proof (larger d_B, s-end avoided) is the paper's. ℕ-floor division and the t ≤ k − 1 range match. |
| `test1At_of_oneEven` | SOUND | The J-form: d_J(r) + 2 = 2k + 1, and all other hypotheses are stated on B = `delVert J z`. It does not need z to be the unique even vertex, so it is more general than the text. |
| Non-vacuity | SOUND | `nonvacuous.lean` instantiates Theorem A on C₄ (k = 2, all hypotheses by `decide`). Order-9 data give 459 instances with a non-empty t-range. |

---

## 2. Findings and fixes

- **F1 (GAP: the collection already claims all of order 9; abstract l. 47–48, Table 1, §6 table, l. 419–421).**
  - **The proposition.** MR **Proposition 139** (p. 150): "Let B be two-connected of order 2k with exactly six even vertices. If an even vertex r of degree six has an even neighbor, then B has at most k paths with at least two ends at r."
  - **Its hypotheses hold at every one of the 1,756 order-9 roots** (`misc_checks.py`):
    - B is 2-connected, since J is 3-connected;
    - the even vertices of B are exactly Z;
    - d_B(r) = 6;
    - r has 5 even neighbours when s ∉ Z (494 roots) and 4 when s ∈ Z (1,262).
  - **The proof is per instance.** Its t = 5 and t = 4 cases are exactly the s ∉ Z and s ∈ Z cases, and their method is close to this paper's: Lovász, then toggling or holding one edge, then a spoke-restoration lemma (Lemma 108).
  - **Thm 144 + Cor 138.** A least failure has d_B(r) ≥ 8, so there is no failure with \|B\| ≤ 8. synthesis §22 (l. 436) already records \|B\| ≥ 12 for the T(6)-i residual.
  - **Consequence.** As read, the unrefereed collection claims Test1 at **all 1,756** roots. "The hypotheses of the collection's dense theorems add 56" and the Table 1 row "A ∪ B ∪ MR 1,658" are literally true, but by omission they suggest that the collection reaches only 123 of the 1,756 roots. The order-9 rows measure the **reach of Theorems A/B**, not new coverage.
  - **Where the theorems are new.** For n ≥ 11 we have d_B(r) = 2k − 2 ≥ 8, and Prop 139 no longer applies. Lean and the unrefereed status also distinguish them.
  - **Fix.**
    - Add Prop 139 (and the Cor 138 / Thm 144 bound) to the §6 table with "1,756 (order 9), 0 (residual)".
    - Say in the abstract and in §5 that at order 9 Test1 is already claimed by the collection (Prop 139) and confirmed by `ret.c`, and that the order-9 numbers test the reach of A and B.
    - Compare the Lovász-and-toggle proof of Prop 139 with Theorems A/B.
- **F2 (ERROR: "a variant with one free path"; abstract l. 50, Results table l. 108, README).**
  - **The bound.** For d_B(r) = 2k − 2 − 2j the count allows up to j free pieces. j = 2 at the 23 degree-3 roots.
  - **What `drm` does.** It allows any number of free pieces.
  - **The data.**
    - All 22 degree-3 successes use **two** free pieces in `drm`'s witnesses.
    - With at most one free piece (a patched copy of `drm`, option `-F 1`; `runs.sh`) the method succeeds at 90 / 90 degree-5 and **15 / 23** degree-3 roots: **105 / 113**, not 112.
  - **Fix.** "A variant with free paths (at most (2k − 2 − d_B(r))/2 of them: one at degree 5, two at degree 3) succeeds at 112 of the 113."
- **F3 (ERROR / overclaim, §7 l. 446–452).**
  - "So at order 9 the frozen roots … are not an obstruction for the Lovász-plus-matching method." The method fails exhaustively at `Huv]z~}` r = 2.
  - Test1 does hold there (`frozen_exception.py`). Take a Walecki Hamilton decomposition of K₇ with x₁x₂ ∈ C₁, x₂w ∈ C₂, wv ∈ C₃. The paths C₁ − x₁x₂, (C₂ − x₂w) + x₂r, C₃ − wv and r x₁ x₂ w v are 4 = k paths with two ends at r, verified from scratch. This is not of the method's form.
  - "Every Lovász path of K₇ minus a 3-matching is Hamiltonian" explains only the 15 matching systems of the 60 per g.
  - **Fix.**
    - Say "with one exception, where Test1 holds by a Hamilton decomposition of K₇".
    - State the Hamiltonian reason only for the matching systems.
- **F4 (ERROR: §8 item 1, l. 459–462: "The proof of Theorem B extends verbatim").**
  - **Why it fails.** Two δ = 1 connectors Q₁ = q₁yq₂ and Q₂ = q₃y′q₄ need y and y′ both to be L-path attachments, or a trivial member lies on a connector and the C-members are not pairwise compatible. If one L-path has ends y and y′, this is impossible.
  - **Instance** (`two_connectors.py`, k = 5, N = {1, …, 8}, s = 9):
    - Q₁ = 7–8–6 and Q₂ = 5–2–3 are vertex-disjoint;
    - every vertex of N is odd in G′ = G − E(Q₁) − E(Q₂);
    - a Lovász decomposition of G′ is {1–3, 2–4–9–1–6–7–3–8, 4–7–2–8–9–5, 6–9–7}, and its L-path 2…8 joins the two interiors.
  - So "every Lovász decomposition works" and the attachment step do not carry over verbatim. A new case is needed, for example choosing D, or allowing an incompatible pair of C-members when u = 1.
  - **Fix.** Replace "extends verbatim" by "extends when no L-path joins two connector interiors; otherwise the attachment step needs a new argument".
- **F5 (ERROR, minor, §5 l. 364).**
  - "52 roots with s ∈ Z where q₁, q₂ are at distance 3 in G": 49 are at distance 3 and **3 at distance 4** (`HsOvEV^` r = 8, `HsQvTin` r = 0, `HsRmvZY` r = 0).
  - **Fix.** "at distance ≥ 3 in G (three at distance 4)".
- **F6 (ERROR, minor, §5 l. 381–382).**
  - "The exact witnesses of `ret.c` have 8 nontrivial members, against k − 1 = 6". The 84 witnesses have 6–10 nontrivial members: one with 6, thirty with 7, twenty-eight with 8, twenty-one with 9, four with 10.
  - k − 1 is 6 at n = 15 and **7** at n = 17. Four witnesses have exactly k − 1 members.
  - None has the end structure of a Lovász family, which I checked; so "not of Lovász type" is right.
  - **Fix.** "6 to 10 nontrivial members (k − 1 = 6 or 7), and none is of Lovász type."
- **F7 (GAP: provenance).**
  - **(a) The data are not in git.** `.gitignore` has `*.out`, so `data/drm9.out`, `drmA9_m0.out`, `drmA9_m1.out`, `frz9.out`, `ret9.out` and `ret_*.out`, all cited by the manuscript and README, are **not in the repository**. Only `frozen9.txt` is tracked.
  - **(b) The residual `drm` runs.** The runs behind "undecided at all 88" and "27 / 7 / 6 frozen undecided" exist only in `/tmp/claude-0/dr`. `run_resid.sh` reads `J_*.g6` and `Jfrozen_*.txt`, which are neither committed nor generated by a committed script.
  - **(c) The recorded commands do not match.**
    - `frz9.out` is reproduced byte for byte by `drm -G` (default L = 3), while the paper says "paths of length ≤ 6". With `-C 60 -L 6` the statuses are identical.
    - `drm9.out` is the run without `-G`, so the 1,756 row has no data file.
    - The `ret.c` commands (budget, `-DWIDE`) are not recorded.
  - **Fix.**
    - Force-add or rename the outputs.
    - Commit the residual outputs and the input-generation commands.
    - Record the exact command for every data file.
- **F8 (NIT, abstract l. 44–45).** "Proved on paper: Theorem B, the case d(z) = n − 3 with s ∈ N(z), by one connector of length at most two" reads as if the case were settled. It holds under the degree condition and only when q₁, q₂ are at distance ≤ 2; 52 order-9 roots have no connector. The same applies to the 73bd190 / 33fc1f0 wording.
- **F9 (NIT, abstract l. 48–49).** "For some choice of connector every Lovász decomposition works at 1,742":
  - at the 481 s ∉ Z roots, Φ = ∅ and there is no connector;
  - `drm`'s Φ has length ≤ 3, not ≤ 2;
  - the choice includes g.
  - **Fix.** "For some choice of g and Φ (Φ ≤ one path of length ≤ 3)".
- **F10 (NIT, Lean descriptions).**
  - (a) `famReassemble` is the forward direction of Lemma 2.2 only; the converse is paper-level and unused by the theorems.
  - (b) `exists_decomp_of_oneEven` is existential; "every Lovász decomposition gives one" is not in the Lean statement, although the proof is generic in D.
  - (c) The parenthetical "(cones, and d(z) = n − 3 with s ∉ N(z))" in the abstract's machine-checked sentence is Lemma 1.1(c), and Cor 3.2 is paper-only.
- **F11 (NIT, hypotheses).**
  - The Setting (l. 63) does not assume J 3-connected or δ(J) ≥ 3. Cor 3.2(b) needs d_J(g) ≥ 3 for g ∈ N ∖ Z (a leaf of J at r would break `hN`). Add "J 3-connected" to the Setting, as the abstract does.
  - Theorem B should state \|B\| = 2k, and "d_B(x) ≥ 2" is redundant there.
- **F12 (NIT, §6 table).**
  - The Thm 50 alternative also needs \|E(G[X])\| ≤ ⌊k²/4⌋ − k − 2.
  - "the floor form of MR Thm 114" should say Thm 144 / 170.
  - Say which collection results were checked for the residual families; Cor 138's list, Prop 139 and Thm 140 do not apply (§1).
- **F13 (NIT, §7).** The clt graph's 2 frozen roots (multi-token table) are neither run nor mentioned.
- **F14 (NIT, wording).**
  - "the coordinator's parity facts" (l. 93) is internal jargon.
  - "Away from cones B − r has many even vertices" (l. 38): there are 1 or 3 at d(z) = n − 3.
  - "DL(1) … open" should note that it fails at universal twins (dl-one).
  - Table 1 has blank cells.
  - Cross-references: the README ("`famReassemble` (Lemma 2.1)") and the `DenseRoot.lean` docstrings ("Lemma 2.1 (families)") use a number that the PDF gives to Definition 2.1; the family lemma is Lemma 2.2.

---

## 3. Attempts to break Theorems A and B (`literal_AB.py`)

| Test | Scope | Result |
|---|---|---|
| Theorem A literally: every Lovász D of G, every tie-break of "larger d_B"; checks: trivial members = {g} ∪ far ends, ⌊d_B/2⌋ paths through x, both \|J_S\| bounds for every S, Hall, reassembly | all 494 order-9 roots with s ∉ Z (459 satisfy the condition) | 188,121 D, 494,342 plans, 0 violations |
| Theorem B literally: every connector of length ≤ 2 making N odd (generic enumeration), every Lovász D of G′, every symmetric choice and tie-break of the case analysis; checks B1–B5 of §1, both bounds for every S, Hall, reassembly | all 2,822 connectors at the 1,262 order-9 roots with s ∈ Z (1,128 with δ = 0, 1,694 with δ = 1) | 730,101 D, 1,828,482 plans, 0 violations |
| Same, random B (d_B(r) = 2k − 2, parities forced; ≤ 300 D and ≤ 4·10⁵ search nodes per instance) | k = 5: 748 Theorem A instances (437 satisfy the condition); 771 + 1,753 connectors (δ = 0 / 1; 358 + 694 satisfy it) | 333,080 D, 1,015,539 plans, 997,879 reassemblies, 0 violations |
| | k = 6: 300 instances (139); 289 + 930 connectors (94 + 256); t = 3, 4, 5 | 57,079 D, 207,137 plans, 206,785 reassemblies, 0 violations |
| | k = 7: 100 instances (41); 94 + 390 connectors (16 + 65); t = 3, …, 6 | 3,494 D, 13,092 plans, 13,092 reassemblies, 0 violations |

Every branch of the Theorem B case analysis is exercised at order 9. Counted in Lovász decompositions per connector:
- δ = 0 with P(q₁) = P(q₂): 65,753;
- δ = 0 with a ≠ b: 247,178;
- δ = 1 with o(y) ∈ {q₁, q₂}: 186,856;
- δ = 1 with o(y) ∉ {q₁, q₂} and P(q₁) = P(q₂): 75,332;
- δ = 1 with o(y) ∉ {q₁, q₂} and a ≠ b: 154,982.

In total, at order 9 alone 1,505,992 reassembled decompositions were checked from scratch (k paths of B, edge partition, exactly two ends at r). A violation of any claimed bound would have been reported even where the degree condition fails; none occurred.

## 4. Reproduction

- **Shipped scripts.**
  - `coverage.py`, `cov1597.py` and `look.py` reproduce every number in Table 1 and the 154 split.
  - `crosscheck.py` gives A 459, B 1,143, 0 mismatches.
- **Independent recount** (`indep_cov.py`, `misc_checks.py`). Every Table 1 entry, 494 / 1,262, the residual counts (42 / 18 / 24 / 4; n = 15 / 17; 7 / 9 / 11 even vertices; \|V(B) ∖ N(z)\| ∈ {8, 10}), MR 47 / 50 / 74 / 166 (0 / 0 / 24 / 111; 123 any; 56 beyond A ∪ B), 3-connectivity of the 1,819 graphs, and the triangle-data identity of the 1,597 roots.
- **`drm` reruns.**
  - The `drm9.out`, `drmA9_m0.out` and `frz9.out` statuses are identical. `drm9.out` and `drmA9_m0.out` are byte-identical; `frz9.out` is byte-identical to `drm -G`.
  - `-G` gives 1,756 YES.
  - `-A -m 0` gives 1,742 ALLD = 1, 481 of them with s ∉ Z.
  - Frozen `-G -C 60 -L 6` gives 112 / 1, the same as shipped. `-F 1` gives 105 / 8 (F2).
- **Witnesses, from scratch.**
  - `drm -G -v`: 1,756 / 1,756 verified. Φ pairs EG ⊕ {g}, D0 is Lovász, and my own family search and Lemma 2.2 assembly give a valid decomposition of B.
  - Frozen: 112 / 112.
  - Negative controls: 300 corrupted witnesses are all rejected; the 1,920 + 2,816 Lovász decompositions at two `-G` roots are all rejected.
  - `ret.c` witnesses: 1,756 + 39 + 17 + 24 + 4 verified.
- **Lean.** Compiled; axioms, signatures and non-vacuity are in `axioms.lean` and `nonvacuous.lean`.

## 5. Notes on the auditor's runs

- **The random runs.** The k = 5, 6 and 7 runs in §3 use `literal_AB.py rand K COUNT SEED 300 400000` (seeds 11, 12, 13).
- **Earlier runs.** Before I fixed a slowness in my own enumerator (the cap was not checked inside path extension), I also ran k = 5 (seed 11), k = 6 (seeds 12, 21) and k = 7 with a smaller node budget. All gave 0 violations.
- **The order-9 run** is unaffected by that fix, since the cap is never reached at order 9. Rerun with the final script, it gave identical totals.
