# A31 — Audit of re-tight (manuscript, `RETight.lean`, scripts, data)

Date: 2026-11-27. Referee stance: adversarial. Grades: **SOUND**, **GAP** (fixable), **ERROR** (false as stated), **UNCLEAR**, **OVERCLAIM** (true content, overstated).

**Version.** Audited at **61dbe23**: `re-tight.tex`, 492 lines, md5 `49265f9b…`; `re-tight.pdf` from the same commit, 8 pp., md5 `6a6fcfbf…`. I audited a `git archive` snapshot, because another session was editing `scripts/ret.c` in the working tree during the audit. Commit **376ea05** landed during the audit. It fills the order-12 placeholders, adds a graph6 length check to `ret.c` and adds `run_roots.py`. I checked its new numbers separately (§5). Outside the two §5.3 paragraphs, the manuscript did not change.

**Numbering.** "l." is `re-tight.tex` at 61dbe23. Statement numbers follow the compiled PDF: Lemmas 2.1–2.2, Thm 3.1, Remark 3.2, **Cor 3.3**, Remark 3.4 ("what is new"), Prop 4.1, Ex 4.2, Conj 6.1. The brief, the README and `coverage.py` call the corollary "Cor 3.4" (see F2).

**Auditor files** (`research/audit/A31-scripts/`; scratch in `/tmp/claude-0/a31`, not committed):
- `runs.sh`: every command the auditor ran.
- `g6.py`, `recount_conditions.py`: own graph6 parser, own 2-connectivity, degeneracy and forest checks, own (∗) and (∗∗).
- `recount.py`: own recount of Table 1, the 77/10/19/58 split, the 147 roots, the −T split and the tight-root counts.
- `lovcheck.c`: an independent enumerator of all Lovász decompositions, with no code shared with `ret.c`. It computes the −T matching (label tie-break), the minimum over **all** orientations allowed by Thm 3.1, and the −L test (all 2^(k−1) orientations, exact general matching).
- `cmp_lov.py`: compares `lovcheck` with `ret −T` / `ret −L` and checks Thm 3.1 under every tie-break.
- `evenn2.c`: a geng filter for even graphs with a vertex of degree n − 2, optionally keeping only those that are not 2-connected.
- `step5.py`: runs the proof of Thm 3.1 literally (Hall matching, Step 5 reassembly) and checks each output decomposition from scratch.
- `ham_frac.py`: a third, Python enumeration of Lovász decompositions, which also counts Hamiltonian paths.
- `verify_lovasz.py`: checks that every −L witness is a Lovász family (`verify_family.py` does not, F3).
- `zcheck.py`: an independent exhaustive re-decision of the −z answers, i.e. of p(B) ≤ k − 1.
- `example42.py`: Example 4.2 and the arithmetic of Prop 4.1.
- `whatsnew.py`: the Remark 3.4 family.
- `samples_check.py`: the order-12/14/16 samples.
- `axioms.lean`: `#print axioms`, signatures, and a non-vacuity instance.

---

## 0. Headline

1. **The mathematics is correct.**
   - I checked every proof line by hand: Lemma 2.1, Lemma 2.2, all five steps of Thm 3.1, Remark 3.2, Cor 3.3, Prop 4.1 (both claims) and Ex 4.2.
   - I checked both reassembly cases, |U| = 1 and |U| = 2. Each gives k paths, with exactly two ends at r: |U| + [|T_U| = 1] = 2.
   - I checked the edge cases k = 2 and k = 3 (the t-range is empty, and ν(Γ) ≥ k − 3 ≤ 0 is trivial).
   - I found no false step in any proof.
2. **I could not break Theorem 3.1.**
   - **Orders 4–8, exhaustive.** I took every even graph with a vertex of degree n − 2, of any connectivity: 2, 10 and 128 graphs. At every (∗∗) root (7, 31 and 252 roots), every Lovász decomposition with every orientation allowed by the theorem (all tie-breaks) gives a path–trivial matching of size ≥ k − 3.
   - **Step 5, literally.** Running Step 5 on these and checking the output from scratch gives a valid k-path decomposition with e(r) = 2 every time (86,193 decompositions).
   - **Order 10, the graphs that are not 2-connected.** I took all 410 of them (495 roots). There is no violation at any of the 465 (∗∗) roots: 451 were enumerated completely and 14 up to 10⁶ decompositions each.
   - **Order 10, 2-connected.** On 615 sampled roots there is no violation either (§3).
3. **The Lean is faithful.**
   - `lake build` is green with 18,414 jobs, and there is no `sorry`, `admit` or `axiom`.
   - All five named theorems depend only on `propext`, `Classical.choice` and `Quot.sound`.
   - Their hypotheses match the paper's exactly. They are satisfiable (instance in `axioms.lean`). `starDel` is B − r with r kept as an isolated vertex, which is harmless.
4. **The checker is sound and, apart from its budget, complete.**
   - Every pruning rule, including two that the paper does not list (F6), is sound.
   - **−T, decomposition counts.** My independent enumerator reproduces `ret −T`'s numbers of Lovász decompositions and its minimum matchings exactly on 871 roots: all 256 at orders 6 and 8, and 615 at order 10, including the 15 failures.
   - **−L at orders 6 and 8.** It reproduces every YES/NO answer.
   - **−z NO answers.** I re-decided all 51 at orders 6 and 8 by my own exhaustive search.
5. **Every headline number I checked reproduces.** That covers:
   - all 24 entries of Table 1;
   - 14,391 positive validations;
   - the −z comparison (256 roots, 51 NO, 0 disagreements; at order 10, 10,017 YES and 234 UNK);
   - 77 = 19 + 58 roots in 10 graphs, all with u ≥ 8;
   - the 147 roots (minimum neighbour degree 6, exactly 3 vertices of degree 8, all YES);
   - −T at order 8 (218/16) and at order 10 (9,905 roots run, 9,884 decided, iff);
   - the order-12 and order-16 samples.
6. **Findings.**
   - **F1 (ERROR).** One false sentence: the order-8 failures are the three graphs with at least **seven** vertices of degree 6, not six; six such graphs exist.
   - **F2 (ERROR).** One wrong cross-reference: eulerian-cone "Theorem 2.3" is Theorem 3.3.
   - **F3 (GAP).** A verification gap: `verify_family.py` does not check the Lovász property. I checked all 15,140 −L witnesses, and all are Lovász families.
   - **F4 (OVERCLAIM).** §6 says the open part has 3 ≤ u ≤ k − 2, but the paper's own u = 1 near-regular graphs are outside (∗∗) and outside Thm 170.
   - **New datum.** One of the 58 undecided order-10 roots is a genuine failure of the method (exhaustive, §4), below the range of Prop 4.1 but inside Cor 168 (F7).
   - **F5 (GAP).** Provenance: the shipped −L/−T outputs are not bit-reproducible from the committed `ret.c`, the budgets in `retL_10` are mixed, and there are no generator commands for the order-12/16 samples.
   - The other findings are minor wording.

## 1. Graded items

### §1–2 Families, Lovász decompositions

| Item | Grade | Notes |
|---|---|---|
| Definition of RE (l. 68–71) | SOUND | Agrees with eulerian-cone Def 1.1 (p_r ≤ \|B\|/2, with e ≥ 1 ⇔ e ≥ 2 for Eulerian B). |
| "Every root of degree n−2 is tight" (l. 77–78) | SOUND | With e = e(r) ≥ 2: e paths end at r, and (2k−2−e)/2 pass through it, so at least k − 1 + e/2 ≥ k paths. The phrase "r is an end of two paths" should read "of at least two" (nit). |
| 14,156 / 300,540 / 14,131 (l. 76–77) | SOUND | 14,149 certified in `re_10_min.tab` + 7 of the 8 budget roots (CB = 5, eulerian-cone l. 604–606) = 14,156. Degree n − 2: 14,129 + 2 (`I]zn^^nzw` roots 0, 1) = 14,131. Note that `budget8_decide.txt` decides RE only: its p column is the witness size (5 at `ITzvn^nzw` r = 4, where p_r = 4). |
| Lemma 2.1 (families) | SOUND | Forward: with ≤ k paths and e(r) ≥ 2, the count forces e(r) = 2, int(r) = k − 2 and no path avoiding r. Converse: concatenation. |
| Lemma 2.2 | SOUND | N has odd degrees in G and s has even degree, so Lovász gives k − 1 paths with one end at each x ∈ N and none at s. By (1), x lies on (d_G+1)/2 = d_B/2 paths. Lean: `lovasz_ends`; the count is inline in `exists_decomp_of_degStar` (`hsize`, `hcount`), with no standalone lemma (nit). |
| "k − 3 path–trivial pairs suffice" (l. 155–156) | SOUND | The ≤ 2 leftover trivial ends pair with each other. |

### §3 Theorem 3.1 and corollaries

| Item | Grade | Notes |
|---|---|---|
| Step 1 | SOUND | D ≠ ∅ since k ≥ 2. |
| Step 2, (3.1) | SOUND | Both ends of every counted path have degree ≥ 2u, and the 2k − 2 ends are distinct. |
| Step 3 (defect Hall) | SOUND | Lean adds two wildcard vertices to every N_Γ(P_i), which is the standard reduction. |
| Step 4 | SOUND | N_Γ(S) = {b_j : j ∉ J}, so we need t + \|J\| ≤ k + 1. For t ≤ 2 this is trivial; for t ≥ 3, t ≤ k − 1. The own-path refinement holds: b_j lies on its own P_j ∉ S, hence on t + 1 paths, hence d ≥ 2t + 2. Second alternative: \|J\| ≤ t + ⌊h_{t+1}/2⌋ ≤ k + 1 − t. |
| Step 5, \|U\| = 1 | SOUND | k − 2 closed-and-continued paths, 1 open path b P a r, and b r: k paths, ends at r = 1 + 1. |
| Step 5, \|U\| = 2 | SOUND | k − 3 + 2 + 1 = k paths. b r b′ has r interior, so the ends at r number 2 + 0. The edges at r are r a_i (k − 1 of them) and r b_j (k − 1), each used once. |
| k = 2, 3 | SOUND | k = 2: P₁, b₁P₁a₁r and b₁r. k = 3: the condition is empty and ν ≥ 0 is trivial. Checked exhaustively on all even graphs of orders 4 and 6 (`step5.py`). |
| "Every D … gives one"; 2-connected ⇒ RE; p(B) ≤ n/2 | SOUND | |
| Remark 3.2 | SOUND; wording | (∗)₃ ⇔ some neighbour of degree ≤ 4 (for k ≥ 4). At t = k − 1 the second alternative fails because k + 1 − 2t = 3 − k < 0, not "since h_k = 0" (F8). |
| Cor 3.3(a), (b), (c) | SOUND | (a): ⌊h_t/2⌋ ≤ 2 ≤ k + 1 − t. (b): h_t = 0 for t ≥ 4, and at t = 3 we need 0 ≤ k − 5. |
| Remark 3.4, the family | SOUND; wrong theorem number (F2) | Degrees: r and s have 2k − 2, V(H) has 6. B is 2-connected and (∗∗) holds at r and at s. It lies in no class of eulerian-cone Thm 3.3: m = 8k − 8 > 3n − 6 rules out planar and K₅-minor-free; δ = 6 rules out 2-degenerate and tw ≤ 3; Δ(B) = n − 2 rules out (e); Δ(B − r) = n − 2 rules out (f); and B − r is not a forest. Checked for H = C₈(1,2) and random 4-regular H on 10, 12 and 14 vertices (`whatsnew.py`). In fact no class contains any member of the family, so "in general" is an understatement. u = 2 < k − 1, so MR Thm 170 and Cor 168 do not apply. |

### §4 Limits

| Item | Grade | Notes |
|---|---|---|
| Hamiltonian members are isolated | SOUND | Every member contains a vertex of G. |
| Prop 4.1, first claim | SOUND | 2(2k−2) + (k−3)(2k−3) = 2k² − 5k + 5 < 2k² − 5k + 6 ≤ m(G), so there are ≥ 3 isolated members and ≤ k − 3 pairs. The hypothesis is vacuous for k ≤ 3 (max m = k(2k−1) − k), so "three Hamiltonian paths" needs no k ≥ 4 caveat. |
| Prop 4.1, complement count | SOUND | m(B̄) ≤ 2k − 4, all degrees in B̄ are odd, and Σ(d̄ − 1) ≤ 2k − 8, so ≤ k − 4 vertices have d̄ ≥ 3. The bound is attained at k = 5, m = 39: the complement is K₁,₃ + 3K₂, with 9 = k + 4 vertices of degree 8. |
| Ex 4.2 | SOUND | m(G) = 2(k−1)², so every path is Hamiltonian and ⌊(k−1)/2⌋ < k − 2 for k ≥ 4. The family for `G]~v~w` (M = {01, 23, 45, 67}) partitions the 18 edges of G and has disjoint pairs {3,7}, {5,6}. It reassembles into 4 paths with e(r) = 2 and is identical to `ret_8.txt`. Vertex 3 is an end of Q₃, Q₄ and Q₅. |
| "Dense instances need … e(x) = 2 at attachments" (l. 300–301) and §6.4 "Equivalently…" | UNCLEAR | F10. |
| Comparison with MR Cor 168 / Thm 170 | SOUND; nits | I read MR pp. 174–179. Cor 168 (any k vertices of degree 2k − 2; exactly two ends at each, none elsewhere) and Thm 170 (k − 1 such vertices plus any positive-degree v) are paraphrased correctly, and "RE at every root" follows. There are 6,131 = 75 + 407 + 5,649 certificates for k = 3, 4, 5, and `small-witnesses.tsv` is not in the repository (`git ls-files`). The "≤ 7 vs ≥ k − 1, disjoint for k ≥ 9" arithmetic is right. "Near-Hamiltonian" and the BR attribution are F11. |

### §5 Computation

| Item | Grade | Notes |
|---|---|---|
| `ret.c` branching | SOUND | An odd vertex of R must end a remaining piece, and all paths from it are tried in both orientations. Otherwise all paths through the lowest edge are tried, each exactly once (left part from a, right part from b). In −L/−T the lowest odd vertex is an unused end in N, so each Lovász decomposition is reached once (confirmed by the exact counts). |
| Pruning: lower bound / distinct attachments | SOUND | max(1, odd/2, max⌈d/2⌉) per component, and every future piece needs its own unused attachment. |
| Pruning: relaxation | SOUND | Replacing each future member by {x} ⊆ Q_x only adds compatibilities. It is disabled in −T. |
| Pruning: capacity ≤ k (k − 1 in −z) | SOUND | Two members on the same path of B are disjoint. In −T it is still on, which is sound: v ∈ N lies on d(v)/2 + [trivial] ≤ k members of a Lovász family. |
| Pruning: end capacity min(d, 2T − d) | SOUND | e_B(v) = (far ends at v) + [Q_v trivial]. The future lower bounds hold (an unused attachment with d_R even gets ≥ 1 more far end or is trivial). In a Lovász family e_B ≤ 2 ≤ cap, so −T loses nothing. |
| Pruning: dead members; Lovász feasibility | SOUND, but not described in the paper | F6. |
| Leaf matching | SOUND | `match_rec` exhaustively decides "≤ u unmatched"; the −T Kuhn search is correct. |
| −z ⇔ p(B) ≤ k − 1 | SOUND | Each path uses ≤ 2 of the 2k − 2 edges at r. |
| −L, −T | SOUND | −T fixes the label tie-break, which is one of the orientations covered by Thm 3.1. |
| `verify_family.py` | SOUND for RE; GAP for −L claims | F3. |
| `compare_z.py` | SOUND here; latent bug | It ignores re.c's status column, so an UNK line (p = −1) would count as "p ≤ k − 1". Not triggered: the 3 UNK graphs of `p_10.txt` are not in `retz_10_partial` (F5). |
| Validation: 4 + 22 + 234 + 14,131 = 14,391 YES, all witnesses pass | SOUND | Re-run. |
| Validation: −z at orders 6, 8: 256 roots, 51 NO, 0 disagreements | SOUND | Re-run with `compare_z.py`. All 256 were also re-decided independently by `zcheck.py`. |
| Validation: −z at order 10: 10,017 YES, 234 UNK at 2·10⁷ | SOUND | No NO answer was tested at order 10. The 11 graphs (90 roots) with p(B) = k were not reached (F9). |
| Table 1, all rows | SOUND | Recomputed with own code and identical to `coverage.py`; `cov_10.txt` reproduces byte for byte. Side remark: at orders 8 and 10 the "lit." roots are a subset of (∗∗). |
| 14,054 / 77 / 10 graphs / u ≥ 8 / 19 (m ≥ 39) / 58 (m ∈ {36, 37, 38}) | SOUND | 49 UNK at 2·10⁸ and 28 at 2·10⁷ (the 19 and the 9 roots of `I]~vvvz}w`). The auditor decided one of the 58 (`ITm~vvz}w`, r = 0): an exhaustive search over all 22,764,672 Lovász decompositions × 16 orientations shows the method **fails** (§4). |
| 13,507 (95.6%), 13,984, 147 | SOUND | Each of the 147 has minimum neighbour degree 6, u = 3, m ∈ {31, 32, 33}, and is YES. None is in tw ≤ 3 or K₅-minor-free either (m > 24 = 3n − 6), so "outside all three" holds even for the full literature list. |
| −T sharpness, order 8 | SOUND numbers; ERROR in description | 218 work and 16 fail, ⇔ (∗∗). The failures are the roots of `G]zn^[`, `G]~vvs` and `G]~v~w` (u = 7, 7, 8), see F1. |
| −T sharpness, order 10 | SOUND | 9,905 lines: 9,884 DONE (9,869 (∗∗) with every D working, 15 ¬(∗∗) with some D failing) and 21 UNK. |
| Order 12, dense sample | SOUND numbers; provenance GAP | 400 distinct graphs, all in the eulerian-cone dense family, 2-connected, Eulerian, m ≥ 45, 1 ≤ u ≤ 4, 793 roots, all YES and Lovász-verified. (∗∗) fails at 589 of them. No sampling seed or command (F5). |
| Order 12, random | placeholder at 61dbe23 | RAND12YES/TOT/MID/UNK. The checkable facts are 711 graphs = exactly those of `re_rand_12` with a degree-10 vertex, and 2,135 roots. Filled in at 376ea05 (§5). |
| Order 12–16 near-regular, u = 1 | SOUND | 40 graphs of the stated shape, 2-connected. All are YES, at most 320 nodes, Lovász-verified. (∗∗) fails at every one (relevant to F4). |
| Order 16, mixed u = 2..6 | SOUND numbers; placeholder M16TEXT; provenance GAP | −L: u = 2, 3: 6/6; u = 4: 1/6; u = 5, 6: 0/6, UNK at 2·10⁷. General checker: 22/30, with 8–12 nontrivial pieces. The 22 is the general checker alone: at one u = 2 and one u = 3 graph it is UNK at 2·10⁸ although −L found a Lovász family. So RE is known at ≥ 24/30 (nit). `near_regular.py` cannot generate these graphs (F5). |

### §6 Open problems; Lean

| Item | Grade | Notes |
|---|---|---|
| §6.1 "open part … between three and k − 2 vertices of degree n − 2" | OVERCLAIM | F4. |
| Conj 6.1 | SOUND as stated; wording | It is a finite statement, and for n ≤ 10 it is checked by the −L data (all witnesses Lovász-verified). The order-8 exceptions are decided NO, not "undecided" (u ≥ 7 ≥ k − 1 = 3), so l. 455 should say "fails or is undecided". In effect it is a statement about n = 12 only. F12. |
| `exists_decomp_of_degStar` | SOUND | `hB : ∀ a, Even (B.degree a)`, `2 ≤ k`, `card W = 2k`, `degree r + 2 = 2k`, and `∀ t, 3 ≤ t → t ≤ k−1 → h_t/2 + t ≤ k+1 ∨ h_{t+1}/2 + 2t ≤ k+1` with ℕ-division. Since t ≤ k − 1 the ℕ-subtraction is exact, and the second alternative is false when 2t > k + 1, as on paper. The conclusion `∃ D, D.size = k ∧ D.ends r = 2` is exactly the paper's. |
| `heavyNbrs` | SOUND | `(neighborFinset r).filter (2t ≤ B.degree ·)`, which is h_t with d_B. |
| `starDel` | SOUND | B − r with r kept isolated. Paths avoid r (`GPath.root_notMem_starDel`), and `evenSet` ignores degree 0, so Lovász applies. |
| `rootedDecomp_of_degStar`, `_few_heavy` (`#heavyNbrs B r 3 ≤ 5`), `_deg_le_six` (`5 ≤ k`, neighbours of degree ≤ 6) | SOUND | These are Thm 3.1 and Cor 3.3(a), (b). `RootedDecomp` = (≤ \|W\|/2 paths, ≥ 2 ends at r), with no connectivity hypothesis, as the paper says. |
| `reassemble` | SOUND | It is Step 5 for arbitrary lo/hi orientations and a partial injection σ with lo(σ i) ∉ P_i and 1 ≤ #unmatched ≤ 2. |
| Non-vacuity | SOUND | C₄ = K₄ − M at k = 2 satisfies the hypotheses (decided in `axioms.lean`). |
| Build, axioms, imports | SOUND | `GallaiLean.lean` imports `GallaiLean.RETight` (l. 80). `lake build` completed successfully with 18,414 jobs. `#print axioms` gives [propext, Classical.choice, Quot.sound] for all five theorems, which covers the whole dependency closure. A grep finds no `sorry` or `admit` in any `.lean` file under `lean/GallaiLean/`, and no `axiom` or `native_decide` in `RETight`, `Lovasz`, `PathSurgery` or `Basic`. |

---

## 2. Findings and required fixes

- **F1 (ERROR, §5.2, l. 407).**
  - "The 16 failures are the three graphs with at least six vertices of degree 6."
  - Six 2-connected Eulerian graphs of order 8 have ≥ 6 vertices of degree 6. `GTz~v[`, `GTm~vs` and `G]zl|{` have exactly 6, and **all their roots work for every D**. The 16 failures are all the roots of `G]~v~w` = K₈ − M (8), and five roots of `G]zn^[` and three of `G]~vvs` (u = 7 each).
  - They are exactly the ¬(∗∗) roots, i.e. the roots all of whose six neighbours have degree 6.
  - **Fix.** "…are the roots all of whose neighbours have degree 6; they lie in the three graphs with at least seven vertices of degree 6."
- **F2 (ERROR, cross-reference; l. 256, l. 385; `coverage.py` docstring; README).**
  - "eulerian-cone Theorem 2.3" / "Thm. 2.3" should be **Theorem 3.3** ("RE from the literature", eulerian-cone.pdf p. 5). The PDF has no Theorem 2.3: §2 has Props 2.1–2.5 and Cor 2.6.
  - In the README ("Cor 3.4(a)", "Cor 3.4(b)") and in `coverage.py` ("Corollary 3.4(c)"), the corollary is Cor 3.3 in the PDF. Remark 3.4 is "what is new".
  - **Fix.** Use `\ref`-stable wording, or correct the three files.
- **F3 (GAP, verification of the method; l. 357–358, 392–393).**
  - "every witness passes `verify_family.py`" is used to certify the **method** (−L). `verify_family.py` checks only that the family is an RE family.
  - It does not check that the pieces form a Lovász decomposition, i.e. that there are k − 1 nontrivial members, each x ∈ N is an end of exactly one, s of none, and the trivial members are the far ends. A bug in `ret.c`'s −L restriction would go unnoticed.
  - I checked all 15,140 −L witnesses shipped at 61dbe23 with `A31-scripts/verify_lovasz.py`: 22 + 218 + 14,054 at orders 6, 8, 10, 793 for mid12, 40 for nr and 13 for mixed16. **All are Lovász families**, as are the 1,504 in `retL_rand12_all` (376ea05). So no claim changes.
  - **Fix.** Add a `-L` flag to `verify_family.py` with these checks, and say in §5.1 that −L witnesses are checked for the Lovász property.
- **F4 (OVERCLAIM, §6 item 1, l. 443–444).**
  - "The data locate the open part: dense graphs, all degrees close to n, with between three and k − 2 vertices of degree n − 2." This is the order-10 picture: there, every root outside (∗∗) ∪ Thm 170 ∪ lit has u = 3 exactly.
  - The paper's own near-regular instances (§5.3, `nr12/14/16`) have u = 1, and (∗∗) fails at all 40 (`samples_check.py`). So they are outside the theorem and outside Thm 170: unproved, although the method succeeds there at once.
  - At 376ea05, 848 random order-12 roots with u ≤ 4 also fail (∗∗).
  - **Fix.** Say where the *method* struggles (3 ≤ u ≤ k − 2 at orders ≤ 16 tested). Separately say that the *unproved* region is ¬(∗∗) ∧ u < k − 1, which contains u = 1 near-regular graphs.
- **F5 (GAP, provenance and reproducibility).**
  - (a) **Not bit-reproducible.** The committed `ret.c` reproduces `ret_8.txt`, `retz_8.txt` and the nr12 part of `retL_nr.txt` byte for byte, but not `retL_8.txt` or `retT_8.txt`. All statuses and all `lovasz=`/`minmu=` values agree. The witnesses and node counts differ: for example `G?bDnw 7` gets a different family, and `G?BDz{ 6` takes nodes = 58 instead of 64. So the shipped −L/−T outputs come from an earlier `ret.c`. A 150-graph order-10 sample (222 roots) run with the committed `ret.c −L` agrees on every status.
  - (b) **Mixed budgets.** `retL_10.txt` mixes budgets: 28 UNK at 2·10⁷, 49 at 2·10⁸. `run_all.sh` says `-b 200000000` throughout. The text's "2·10⁷ to 2·10⁸" is accurate, but `run_all.sh` does not produce the shipped file.
  - (c) **No generator commands.** There are none for `mid12_sample.g6` ("random sample", no seed), `mixed16.g6` (attributed to `near_regular.py` at l. 422, which only makes a single complement degree C), `m16_u4.g6` and `m16_u6.g6`. `run_all.sh` defers to "the manuscript, §5.3", which gives no commands.
  - (d) **`compare_z.py` ignores the status column** of `re.c −p` (an UNK line, p = −1, would count as "p ≤ k − 1"). Not triggered.
  - **Fix.** Record the `ret.c` version, or regenerate the order-6/8/10 −L/−T files with the committed binary. Record per-file budgets. Add the sample generators and seeds to `run_all.sh`, and in `compare_z.py` skip lines whose status is not OK.
- **F6 (GAP, description of the checker, l. 339–347).**
  - The list of pruning rules omits two that `ret.c` uses:
    - the dead-member count: members that meet every placed piece and every unused attachment are isolated, and more than u of them prune; this is off in −T;
    - the −L feasibility test per component C of R: o_C ≥ 2, d_C(v) ≤ o_C, \|E(C)\| ≤ (o_C/2)(\|C\| − 1).
  - Both are sound. The paper should also say that −T keeps the capacity, end-capacity and lower-bound rules, and why they lose no Lovász decomposition (see §1).
  - **Fix.** Add the two rules with one-line soundness arguments.
- **F7 (OVERCLAIM, mild, abstract l. 51–54).**
  - "Its failures are dense: near-complete graphs force Hamiltonian Lovász paths, which are compatible with nothing."
  - In the shipped data, no order-10 failure is decided by search: all 77 non-successes are UNK. The 19 with m ≥ 39 fail by Prop 4.1. For the 58 with m ∈ {36, 37, 38}, the Hamiltonian argument does not apply: m(G) = 28–30 < 4 · 8 does not force a Hamiltonian path.
  - The auditor decided one of the 58 exhaustively (`ITm~vvz}w`, r = 0, m = 36; §4): the method **fails** there. So failures do occur below the Prop 4.1 range, and the paper can say so once the 58 are decided. There, 15% of the Lovász decompositions have no Hamiltonian path and still fail, so "force Hamiltonian Lovász paths" is not the whole mechanism.
  - At order 8 the mechanism is real: every Lovász decomposition at the 16 failing roots contains a Hamiltonian path (`ham_frac.py`: 960, 1,920 and 2,816 decompositions, all with one).
  - "Complementary" is fine as a description of regimes. But the abstract does not say that MR is unrefereed, and it does not mention that at n = 16 the method is undecided at u = 4–6, below Thm 170.
  - **Fix.** "Its known failures are dense …; at order 10, 58 dense roots remain undecided." Add "(unrefereed)" after the MR citation in the abstract.
- **F8 (wording, Remark 3.2, l. 235–236).** "At t = k − 1 only the first alternative can hold when k ≥ 4, since h_k = 0." The reason is k + 1 − 2(k−1) = 3 − k < 0. h_k = 0 always holds and does not matter here. **Fix.** "since k + 1 − 2t < 0".
- **F9 (wording, §5.1 "Negative answers", l. 368–369).**
  - The order-10 sentence validates no negative answer. All 10,017 decided roots lie in graphs with p(B) = k − 1 (9,899 of the 9,913 graphs; re.c OK).
  - The run stopped before reaching any of the 11 graphs with p(B) = k, where −z must say NO (90 roots), or any of the 3 graphs where `re.c −p` is UNK.
  - **Fix.** Say so: "no NO instance was reached at order 10".
- **F10 (UNCLEAR, l. 299–301 and §6 item 4, l. 466–467).**
  - "Dense instances need pieces that end several times at one vertex, that is, decompositions of B with e(x) = 2 at attachments." And: "Equivalently, the decomposition of B has e(x) = 2 at a vertex whose piece is nontrivial."
  - For x ∈ N with Q_x nontrivial, the number of piece ends at x is 1 + e_B(x), so "end of three pieces" ⇔ e_B(x) = 2 is right there.
  - But a non-Lovász family can also arise in two other ways: s can be an end of ≥ 2 pieces (e_B(s) ≥ 2), or a trivial x can be an end of ≥ 3 pieces (e_B(x) ≥ 4). So "that is" / "equivalently" are too strong.
  - "Need" is proved only for the cocktail party graph (Ex 4.2) and the Prop 4.1 range.
  - **Fix.** "A non-Lovász family has a vertex of N that ends ≥ 3 pieces, or s ending ≥ 2. For x ∈ N with Q_x nontrivial the former is e_B(x) = 2."
- **F11 (nits, MR comparison and bibliography, l. 319–320, 488–489).**
  - MR (p. 174) proves Lemma 167 with its own integral-flow detachment and cites Bahmanian–Rodger [3, Thm 3.1] for the general connected balanced detachment. "(Bahmanian–Rodger)" should say "after".
  - "Near-Hamiltonian paths" is stronger than MR's "every path visits all of R", where \|R\| = k or k − 1, about half the vertices.
  - `\bibitem{BR}` is never cited.
  - **Fix.** "paths that all visit R (MR's detachment, after [BR])", with `\cite{BR}`.
- **F12 (nits).**
  - l. 455: "Every root left undecided" should be "every root at which the method fails or is undecided" (the order-8 cases are NO).
  - l. 129–130: "Only the direction 'family ⇒ RE' is used below" — the checker's exactness, its NO answers and the −z equivalence use "RE ⇒ family" too.
  - l. 430–431: "finds families for 22 of the 30" — RE is known at ≥ 24/30 when the −L successes are counted.
  - Results table, Lemma 2.2 "Lean": inline, not a named lemma.
  - Placeholders at 61dbe23: RAND12YES, RAND12TOT (= 2,135), RAND12MID, RAND12UNK, M16TEXT (flagged, not graded; filled at 376ea05).

## 3. Attempts to break Theorem 3.1

| Test | Scope | Result |
|---|---|---|
| Every Lovász decomposition, every orientation with d(b) ≤ d(a) (all tie-breaks), path–trivial matching ≥ k − 3 (`lovcheck.c`) | All even graphs (any connectivity, `nauty-geng` + `evenn2`) with a vertex of degree n − 2: n = 4 (2 graphs, 7 roots), 6 (10, 31), 8 (128, 275) | All 290 (∗∗) roots hold. All 23 ¬(∗∗) roots at n = 8 have a failing D. |
| Same | n = 10, all 410 even graphs with a degree-8 vertex that are not 2-connected (495 roots), cap 10⁶ decompositions per root | 465 (∗∗) roots: no violation (451 complete, 14 capped). 30 ¬(∗∗) roots: all have a failing D. |
| Same | n = 10, 2-connected: the 15 −T failures plus 600 random −T DONE roots with ≤ 3·10⁵ decompositions (seed 31) | No violation. Counts and minmu equal ret −T at all 615. |
| Step 5 run literally, output checked from scratch (`step5.py`, networkx Hopcroft–Karp) | All (∗∗) roots of all even graphs of orders 4–8, ≤ 2,000 decompositions per root (none exceeded), all theorem orientations | 7 + 144 + 86,042 decompositions, each with all orientations: every output is k paths of B partitioning E(B) with e(r) = 2. |
| Remark 3.4 family | H = C₈(1,2) (n = 10), both roots, first 3·10⁵ decompositions; random 4-regular H on 10 vertices (n = 12), both roots, first 10⁵ decompositions | muA = 2 = k − 3 at n = 10, and muA = 3 = k − 3 at n = 12. OK. |

Since the theorem is also checked in Lean, these runs are sanity checks of the statement–formalisation match, and they confirm it.

## 4. Computation: reproduction

- **Shipped checkers on shipped data** (`runs.sh`):
  - `verify_family.py`: 4 + 22 + 234 + 14,131 = 14,391 / 0 failures; −L: 22, 218, 14,054, 793, 40, 13; general mixed16: 22; −z: 11 + 194 + 10,017.
  - `compare_z.py`: 22 agree (11 NO), 234 agree (40 NO), and at order 10: 10,017 agree, 234 UNK.
  - `coverage.py`: Table 1 exactly; `cov_10.txt` byte-identical.
  - `check_star.py`: order 8: 218 / 16, no violation; order 10: 9,869 + 15, 21 UNK, no violation.
- **Own recount** (`recount.py`, with planarity the only library call): every Table 1 entry, and every claim in §5.2 on the 77, 19, 58 and 147 roots. The tight-root counts are as in §1.
- **Independent enumerator vs ret −T.** The decomposition counts and minmu agree on 22 + 234 + 615 roots. A third, pure-Python enumeration (`ham_frac.py`) agrees at the four roots I tried (15, 960, 1,920, 2,816).
- **−L vs ret −L.** YES/NO agree at all 256 roots of orders 6 and 8: 16 NO, all within Cor 168. My exhaustive enumeration confirms the 16 NO. The committed `ret.c −L` on a 150-graph order-10 sample (222 roots) gives YES everywhere, as shipped.
- **−z.** `zcheck.py` re-decides p(B) ≤ k − 1 by its own exhaustive search for all 102 + 6 graphs: 256/256 agree, including all 51 NO.
- **One of the 58 undecided order-10 roots, decided.** `ITm~vvz}w`, r = 0 (m = 36, u = 8) has **22,764,672** Lovász decompositions. `lovcheck` enumerated them in 170 s.
  - The exhaustive −L run took 13 CPU-minutes. It tried every decomposition and all 16 orientations, with an exact general matching, and found **no family with k − 2 = 3 pairs**: the method **fails** there.
  - The path–trivial matching is ≤ 1 for every D and every orientation.
  - 19,332,864 of the decompositions (84.9%) contain a Hamiltonian path of G. The other 3,431,808 contain none and still fail, so the Hamiltonian mechanism does not explain this failure on its own.
  - `lovcheck`'s −L agrees with `ret −L` at all 256 roots of orders 6 and 8, including the 16 NO.
  - So at least one of the 58 is a genuine failure outside the range of Prop 4.1. It lies inside Cor 168 (u = 8 ≥ 5), so the abstract's "succeeds at every root outside Cor 168" survives.
  - The other 57 can be decided the same way, at about 15 CPU-minutes each. Not done here, because the CPU was shared.

## 5. Addendum: commit 376ea05 (landed during the audit)

The new order-12 random paragraph checks out against `retL_rand12_all.txt.gz`:
- 2,135 roots of degree 10 in the 711 graphs.
- The 1,119 roots outside Thm 170 (u ≤ 4) are all YES. (∗∗) fails at 848 of them.
- 514 roots inside the Thm 170 range were run: 385 YES, 129 UNK at 2·10⁷.
- 502 roots were not run (1,119 + 514 + 502 = 2,135).
- All 1,504 witnesses are Lovász families.

The new M16 sentence ("two runs of 3·10⁹ nodes … still undecided") matches the empty `retL_m16_u4/u6.txt` at 61dbe23. The `ret.c` change is a graph6 length guard. It fixes a latent out-of-bounds write in `parse_g6` for n > 16 at 61dbe23, which no shipped input triggers. F1–F12 are unaffected by 376ea05.

---

## 6. Fixes applied (re-tight session, after the audit)

- **F1.** §5.2 now says that the 16 order-8 failures are exactly the roots all of whose neighbours have degree 6. They are all roots of K₈ − M plus eight roots of two graphs with seven vertices of degree 6. The sentence also adds the Hamiltonian-path observation (`ham_frac.py`).
- **F2.**
  - "eulerian-cone Theorem 2.3" is now Theorem 3.3 in Remark 3.4 and in the caption of Table 1.
  - The README and `coverage.py` now say Cor 3.3.
- **F3.**
  - `verify_family.py -L` checks the Lovász property: k − 1 nontrivial members, every x ∈ N an end of exactly one, s of none, and trivial members = far ends.
  - It passes on every −L witness: 22, 218, 14,054, 793, 40, 13 and 1,504.
  - As a negative control it rejects 125 of the 234 general RE families at order 8.
  - §5.1 and §5.2 say that −L witnesses are checked this way.
- **F4.** §6 item 1 now separates the two regions:
  - the *unproved* region: ¬(∗∗) and u < k − 1, which contains the u = 1 near-regular graphs;
  - the region where the *method* struggles: its dense part with 3 ≤ u ≤ k − 2, at the orders tested.
- **F5.**
  - The order-6/8 −L/−T files were regenerated with the committed `ret.c`.
  - `run_all.sh` records the shipped budgets: retL_10 mixes 2·10⁸ and 2·10⁷, retT_10 is partial, and rand12 is partial inside the Thm 170 range.
  - New `samples.py` reproduces all eight sample inputs byte for byte (seeds inside). The manuscript cites it instead of `near_regular.py`.
  - `compare_z.py` skips graphs whose p(B) is not OK in re.c.
- **F6.** §5.1 lists the dead-member rule and the per-component Lovász rule, each with its soundness argument. It also says which rules −T keeps and why they lose no Lovász decomposition.
- **F7.** The abstract now says "known failures", names the 58 undecided dense roots at order 10, marks MR as unrefereed, and mentions the order-16 u = 5, 6 cases.
- **F8.** Remark 3.2 gives the reason as k + 1 − 2t < 0.
- **F9.** §5.1 says that no NO instance of −z was reached at order 10.
- **F10.** Ex 4.2 and §6 item 4 now give the correct characterisation of non-Lovász families: a vertex of N ending ≥ 3 members, or s ending ≥ 2. They state "need" only for K₂ₖ − M and the Prop 4.1 range.
- **F11.** The MR comparison now says "MR's own integral-flow detachment, after Bahmanian and Rodger" and "k paths that all visit R, |R| ∈ {k − 1, k}". `\cite{BR}` is used, and the reference is copied from MR's bibliography.
- **F12.**
  - Conj 6.1's evidence now says "fails (order 8) or is undecided (order 10)" and "in effect a statement about n = 12".
  - §2 says that the checker uses both directions of Lemma 2.1.
  - The order-16 text says that RE is witnessed at 24/30 (22 general, plus 2 found only by −L).
  - The results table says the Lemma 2.2 count is inside the Lean proof of Thm 3.1.
  - The intro now reads "at least two paths".
  - The two 3·10⁹-node order-16 runs finished undecided, and the manuscript says so.
- **New datum (§4, after the report).** The manuscript (§5.2, abstract), E32 and synthesis §29 now record the exhaustively decided failure at `ITm~vvz}w` r = 0, the 15% of decompositions there with no Hamiltonian path, and 57 (not 58) undecided roots.
