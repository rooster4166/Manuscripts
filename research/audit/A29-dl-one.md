# A29 — Audit of dl-one (manuscript, `DLOne.lean`, scripts)

Date: 2026-11-27. Referee stance: adversarial. Grades: **SOUND**, **GAP** (fixable), **ERROR** (false as stated), **OVERCLAIM** (true content, overstated), **MINOR**.

**Version.** Branch `claude/dl-one`, commit **5d81e14** ("manuscript draft, README, E31; Conjecture SF ..."). The author session edited the files while the audit ran:
- I started on an untracked draft (tex md5 `3238305d…`, 581 lines). It had no Conjecture SF or Proposition 9.5.
- The tex, README and E31 were then committed in 5d81e14, together with a `dl.c` that has the `sepfar` mode. The Lean change in that commit is docstring only.
- **Everything below refers to 5d81e14.** I confirmed that the files on disk equal HEAD at the end of the audit:

| file | md5 |
|---|---|
| `manuscripts/dl-one/dl-one.tex` | `e3828ccc722ad06302b49fce15ecff95` |
| `manuscripts/dl-one/dl-one.pdf` | `bdd86fd2d439e66d6d36010adf03478c` |
| `lean/GallaiLean/DLOne.lean` | `cf101ce8a1bced7fda1f86da2ad09c47` |
| `manuscripts/dl-one/scripts/dl.c` | `adbba60265284b4599579281bf6c8d6f` |
| `manuscripts/dl-one/README.md` | `bb429cfbd1423899de1376199e528656` |
| `manuscripts/l1-induction/scripts/moves.h` | `0beba7992062aaeb5e77baf1baec0a77` |

- The PDF is in sync. I recompiled the tex three times in a scratch copy, and the `pdftotext` diff against the committed PDF is empty.
- The only warnings are four hyperref "Token not allowed" warnings. There are no undefined references and no overfull boxes.

**Numbering.** The brief's numbers are those of an earlier draft. In the compiled PDF:
- the brief's "Proposition 8.2" (near twins) is **Proposition 9.2**;
- the brief's "Section 10 table" is **§11 Formalisation**;
- the residual section is **§10**;
- the new statements are **Conjecture 9.4 (SF)** and **Proposition 9.5** (SF ⇒ S_b). I audited them too.

"l." below means a line of `dl-one.tex` at 5d81e14.

**Auditor files.** `research/audit/A29-scripts/` contains:
- `filt.py`: filters geng output to graphs with exactly one even vertex;
- `stats.py`: the §8 structure statistics from `dl -m pairs`;
- `ex.py`: checks the examples;
- `sep1_reason.py`: tests the §10.4 "local reason";
- `vacuous_rob.py`: compares the robustness definitions;
- `cert_sound.py`: certificate soundness;
- `make_variants.sh`: builds three auditor variants of the authors' code in a scratch copy (true L1* local form; CN1 `both` restricted to d ≥ 3; `dlrec` printing both orientations).

The authors' code was compiled unmodified in a scratch copy (`gcc -O2`, `g++ -O2 -I ../../l1-induction/scripts`). Order 11 was **not** run, as instructed.

---

## 0. Headline

1. **Every proof on paper is correct.** I found no mathematical error in Prop 3.1, Lemmas 4.1–4.2, Thm 5.1, Thm 6.1, Cor 6.2 (both parts), Prop 7.1 (including the non-twin claim), Cor 7.2, Prop 9.2 or Prop 9.5.
   - The cited statements are used within their hypotheses: Fan's lemma with end paths, the separation theorem, L1 and the leaf merge.
   - There are small gaps of statement hygiene: an implicit "g even", isolated vertices in Cor 7.2, and SF/CN1 without "non-adjacent" (F11, F12, F16).
2. **The Lean is faithful, compiles, and uses standard axioms only.**
   - `lake build` of the full library is green (18,408 jobs).
   - `lake env lean GallaiLean/DLOne.lean` has no errors.
   - The file contains no `sorry`, `admit`, `axiom`, `native_decide` or `implemented_by`.
   - All 19 theorems depend at most on `propext`, `Classical.choice` and `Quot.sound` (`reachable_mem_of_closed` on none).
   - The statements match the §11 table. The one weakening: Prop 7.1 says "with the same disjunct", which `disjL1_free_target` does not state (F7).
3. **Every number I re-ran reproduces exactly.** This covers all §8 and §9 numbers and the order ≤ 7 numbers of §10.
   - Two independent soundness checks pass: the certificate calculus is never contradicted by the exact solver (327,634 certified orientations, 0 unsound), and the input lists are complete up to isomorphism.
   - But one explanatory claim is **false**: §10.4's "local degree-two reason" fits only 14 of the 118 instances (F1).
   - "The smallest is DEk" is false (F2).
   - The "local form of L1*" count tests a weaker statement (F8). The true local form also holds, in 86,882 queries.
4. **Overclaims.**
   - The order-11 boundary is in the title and abstract while it is "pending". The README lists it as verified. The four-slice certificate claim has no data (F5).
   - "Open core" / "What remains" omit two open regions: the d(g) = 2 core with a second common neighbour (F3), and a ∉ N(g) or b ∉ N(g), which reduce only to the open L1* (F4).
   - "For items 1–5, also in Lean" overstates the formalisation (F6).

## 1. Verdict per claim

| Claim | Verdict | Notes |
|---|---|---|
| Def 1.1, Conj 1.2 | SOUND | `UnivTwins`, `TriangleDisj D [(a,b)]` and `DisjL1` match exactly. |
| Lemma 2.1 (Fan with end paths) | SOUND as cited | Hypothesis b(g) = 1 > Z(u) = 0 holds: every neighbour of u other than g is odd. Matches CLT Thm "Fan with end paths" and RD Lemma 2.2. Used with u = a in Prop 9.5 (F16). |
| Thm 2.2 (separation) | SOUND as cited | RD Thm 6.1 = `separation_set` (`Packed`). |
| Prop 3.1 | SOUND | §2.1. Lean covers the connected form only, as stated. |
| Lemma 4.1 (leaf exchange) | SOUND | `leaf_exchange` matches verbatim. |
| Lemma 4.2 (NP) | SOUND | `not_paired_adj` matches. Abstract wording: F13. |
| Remark 4.3 | SOUND | |
| Thm 5.1 | SOUND (MINOR: g even is implicit) | Lean has `hg : g ∈ evenSet G` (F11). |
| Thm 6.1 | SOUND | `avoid_deg_two` matches. b odd follows automatically. |
| Cor 6.2, first part | SOUND | `disjL1_deg_two`. |
| Cor 6.2, second part | SOUND (paper only, as stated) | "More generally" is a misnomer (F17). |
| Prop 7.1, transfer | SOUND | `disjL1_free_target`, minus "same disjunct" (F7). |
| Prop 7.1, child never twin | SOUND (paper only, as stated) | §2.4. |
| Remark after 7.1 (u ∉ N[b] ∪ {a} carries S_b) | SOUND | Exactly the hypotheses of `csys_caseI`. |
| Cor 7.2 | SOUND except "connected" | Isolated vertices (F12). |
| §8 solver, validation, table | SOUND, with wording issues | §4. "942 pairs" is 942 of 968 (F9). |
| §8 "decide DL(1) for every graph on ≤ 10 vertices" | SOUND | Orders 1 and 3 are trivial: only P3, and its one pair is the twin pair. |
| §8 certificates | SOUND | Reproduced; soundness checked (§4.3). Base-case wording: F18. |
| §8 order-11 sentences | OVERCLAIM | F5. |
| §8 Structure | SOUND, not scripted | All numbers reproduced (F10). |
| Conj 9.1 (N), set form, maximal form | Data SOUND | 264,437 / 675,641 / 300,644 reproduced. |
| "local form of L1*, 79,598 queries" | GAP | The code tests a weaker statement (F8). |
| Prop 9.2 | SOUND | |
| Conj 9.3 (CN1), Conj 9.4 (SF) | Data SOUND; statements MINOR | Both are false for adjacent a, b, so "non-adjacent" must be stated (F11). |
| Prop 9.5 | SOUND | Uses the chain mechanism beyond Lemma 2.1's wording (F16). |
| Remark 9.6 | SOUND | The L1S "blocked" definition is paraphrased correctly for A = {x}. "Most" is unquantified. |
| §10.1 numbers, Example 10.1 (FsOrg) | SOUND | Checked by hand and by script. "Minimal": F14. |
| §10.2 numbers, FsPzw | SOUND | Populations differ (F15). |
| §10.3 numbers, DEk | SOUND, except "the smallest" | F2. |
| §10.4 "118 instances" | SOUND | |
| §10.4 "The reason is local: a vertex of degree two …" | **ERROR** | F1. |
| §10.5 summary, §12 "What remains", README "open core" | OVERCLAIM / GAP | F3, F4. |
| Status paragraph "items 1–5, also in Lean" | OVERCLAIM | F6. |
| Title and abstract | OVERCLAIM | F5, F6, F13. |
| §11 Lean table | SOUND | §3. |

## 2. Proofs on paper (details)

### 2.1 Proposition 3.1
- **Order.** N := |C|. Then d(a) = N − 2 is odd, so N is odd. Every vertex of C has positive degree, since every vertex of C − {a, b} is adjacent to a.
- **g ∈ C.** An odd number of vertices, all of positive degree, cannot all be odd. So g ∈ C, and C has N − 1 odd vertices.
- **Counting.** There are (N − 1)/2 paths in C. By (2), (d(a) + 1)/2 = (N − 1)/2 of them contain a. The same holds for b, since d(b) = d(a).
- **Correct.** The Lean `univTwins_every_path` assumes every vertex other than a, b is adjacent to both, that is, V(G) = C. That is the "connected G" form claimed in §11.

### 2.2 Lemmas 4.1, 4.2 and Theorems 5.1, 6.1
- **Lemma 4.1.**
  - The only end at x is on ℓx, so a path R through an edge xz (z ≠ ℓ) has x as an interior vertex.
  - ℓ ∉ R. The split R₁ + xℓ, R₂ keeps the ends.
  - The new path through ℓ ends at an end of R, which is not x.
  - Every new path lies in R ∪ {ℓ}.
- **Lemma 4.2.**
  - In K = H(x;y), only y can be even, possibly isolated if d(y) = 1.
  - ℓ and y are packed: ℓ's only neighbour is x, and x ≁ y in K. Separation applies.
  - The two cases for P are right: a leaf-to-x path is the edge ℓx.
  - After the merge, b(y) = 0 + 1.
- **Theorem 5.1.**
  - In H = G − ga there is no even vertex: d(g) − 1 is odd, provided g is even (F11).
  - The three cases are exhaustive. In the third, N(g) = {a, b} and N(b) = {g}, so the component is a g b.
  - After appending ga to Q_H(g), the only path through a has far end ≠ b.
- **Theorem 6.1.**
  - d_K(a) = d_G(a), d_K(b) = d_G(b) − 1, and g is isolated.
  - Distance ≥ 3 uses N(a) ∩ N(b) = {g}.
  - The exchange preserves separation, since new paths lie in old paths ∪ {ℓ}.
  - The merge needs "no path contains ℓ and b". The leaf path contains a, so this holds.
  - The claim "no path ending at a contains b" is proved correctly.
  - Subdividing ab by g is legal, and R ≠ Q(a).
  - Twins are impossible, since d(a) ≥ 3 and N(a) ∩ N(b) = {g}.

### 2.3 Corollary 6.2
- **First part.** d(a) is 1 or ≥ 3; the two cases are Thm 5.1 and Thm 6.1.
- **Second part.**
  - In G − g + xy there is no even vertex, and a ≁ b, since xy ≠ ab.
  - L1 gives Q(b) ∌ a. Q(b) cannot contain the edge xy if a ∈ {x, y}, because it avoids a.
  - Subdividing adds only g, which is interior with degree 2.
- **Correct.**

### 2.4 Proposition 7.1 and Corollary 7.2
- **Transfer.** By Lemma 2.1, V(Q(b)) ⊆ V(Q′(b)) ∪ {u} with u ≠ a, and likewise for a.
- **Non-twin child.**
  - If u ∈ C′, then u ∈ N(a), which is excluded.
  - Otherwise every vertex of C′ is odd in G − gu: g has degree d(g) − 1, which is odd, and only u can be even. So |C′| is even.
  - Then d(a) = |C′| − 2 would be even, but a is odd. Contradiction.
  - The text says "while d(a) = |C′| − 2 is odd", which inverts the wording, but the logic is right.
  - Remark: the same argument shows that a target adjacent to **at most one** of a, b also has a non-twin child. §10.1 uses this ("using Proposition 7.1 for the twin issue"), but Prop 7.1 only states the case of a target adjacent to neither (F16).
- **Corollary 7.2.** Items (1)–(3) follow as claimed.
  - (2) uses Thm 5.1 with the roles of a and b swapped when needed.
  - (3) is the case split N(g) = {x, y}: an edge; independent and ≠ {a, b}, which is Cor 6.2 part 2; or {a, b}, which is Cor 6.2 part 1 unless there is a second common neighbour.
  - "G is connected" does not follow from edge-minimality (F12).
  - Cor 7.2 does **not** give a, b ∈ N(g) (F4).

### 2.5 Propositions 9.2 and 9.5
- **Prop 9.2.** Contrapositive of Conjecture N in both orientations. Correct. The clause "since a ∉ N(b) …" is unnecessary.
- **Prop 9.5.**
  - G − ga has the single even vertex a, which needs d(a) ≥ 3.
  - Lemma 2.1 with u = a: chain vertices are g and N_{G′}(a). Re-routed paths and Q* are D′-paths that end at chain vertices, because each chain vertex has exactly one end.
  - Q′(b) has ends b and β, neither of which is a chain vertex. So Q′(b) is untouched, and Q(b) = Q′(b) ∌ a.
  - Pairs with a leaf are covered by Thm 5.1.
  - **Correct.** But this uses the chain mechanism of RD Lemma 2.2 / CLT §6, not the wording of Lemma 2.1 (F16).
- **The §10.2 claim** "(1.1) fails exactly when the chain stops at β" is also correct.
  - Q′(b) avoids a, and every re-routed path contains u = a. So Q′(b) can change only by being Q*.
  - If it is Q*, then Q(a) = Q(b) = Q′(b) + βa, and both disjuncts fail.
  - The paper states this without proof (F15).

## 3. Lean faithfulness

### 3.1 Build and axioms
- `lake build`: "Build completed successfully (18408 jobs)".
- `lake env lean GallaiLean/DLOne.lean`: warnings only (deprecations, unused simp args).
- `#print axioms` over every theorem of the file (19):
  - `[propext, Classical.choice, Quot.sound]` for all of them, including `leaf_exchange`, `not_paired_adj`, `avoid_leaf`, `disjL1_leaf`, `avoid_deg_two`, `disjL1_deg_two`, `disjL1_free_target`, `univTwins_every_path` and `not_triangleDisj_of_twins`;
  - except `leaf_path_length_one` `[propext, Quot.sound]` and `reachable_mem_of_closed` (none).
- Library names cited in §1 and §11 exist: `test1At_of_disjL1`, `l1starGen_of_blocked`, `separation`, `separation_set`, `lovasz_avoid_nonadj`, `leaf_merge`, `merge_degrees`, `packed_lift`, `exists_subst_path`, `csys_caseI`.

### 3.2 Statements against the paper

| Paper | Lean | Match |
|---|---|---|
| Lemma 4.1 | `leaf_exchange`: ℓ a leaf at x (`hℓ`), `3 ≤ degree x`, `D.ends x = 1`, P₀ ∈ D of length 1 through ℓ, y ∉ {x, ℓ} ⇒ D′ with the same ends; every path through ℓ avoids y and has no end at x; every path ⊆ an old path ∪ {ℓ}. | exact |
| Lemma 4.2 | `not_paired_adj`: no even vertex, `H.Adj x y`, `3 ≤ degree x` ⇒ Lovász D in which every path ending at y has no end at x. | exact (equivalent to Q(x) ≠ Q(y)) |
| Thm 5.1 | `avoid_leaf`: card evenSet ≤ 1, **g ∈ evenSet**, N(a) = {g}, b odd, a ≠ b, ¬UnivTwins ⇒ Q(b) ∌ a. | exact, with g even explicit (F11) |
| Thm 6.1 | `avoid_deg_two`: g even, N(g) = {a, b}, a ≠ b, ¬ab, common neighbours ⊆ {g}, `3 ≤ degree a` ⇒ Q(a) ∌ b. | exact |
| Cor 6.2 (1) | `disjL1_deg_two`: g even, N(g) = {a, b}, a, b odd, ¬ab, common neighbours ⊆ {g}, ¬UnivTwins ⇒ `TriangleDisj D [(a,b)]`. | exact |
| Prop 7.1 (transfer) | `disjL1_free_target`: g even, gu ∈ E, u ∉ {a, b}, u ≁ a, b, a, b ≠ g, a good child ⇒ a good decomposition of G. | conclusion lacks "same disjunct" (F7) |
| Prop 3.1 (connected) | `univTwins_every_path`, `not_triangleDisj_of_twins`: ≤ 1 even vertex, a ≠ b, ¬ab, a odd, every x ∉ {a, b} adjacent to both ⇒ all paths contain a, b; ¬TriangleDisj. | exact for V(G) = C |

- No hypothesis is vacuous. Each set of hypotheses is satisfiable: K_{2k+1} minus a matching; FsOrg-type graphs; P3 for the leaf lemma.
- Docstrings now cite the correct manuscript numbers. The earlier draft's `avoid_free_target`, which did not exist, is gone.

## 4. Data

### 4.1 Inputs
`stl/scripts/one_even_{5,7,9}.g6` have 7 / 130 / 11,936 graphs. I regenerated the lists from `nauty-geng -c` with an own filter (`filt.py`). They are equal up to isomorphism (`nauty-labelg`, sorted diff empty). The labellings differ.

### 4.2 Reproduced exactly (authors' code, unmodified)

| Claim | Command | Result |
|---|---|---|
| Table rows 5, 7, 9 | `dl -m sum` | 21/3/3, 947/14/14, 166,217/170/170. No MISMATCH line. Order 9 in 11 s. |
| Brute force against the solver | README commands | "compared 942 mismatches 0 onlyA 26": 8 graphs are skipped as `toolarge` (F9). |
| enum.c against brute | own loop | 129/129 graphs, counts equal. |
| Certificates | `dlrec BMS`, orders 5, 7, 9 | 18, 933, 166,047 certified, 0 uncertified (order 9 in 73 s). |
| Structure | `dl -m pairs` + `stats.py` | 166,998 non-twin pairs; 6,221 failing orientations, all satisfying the three conditions; 5,648 successes with the three conditions; 85,139 / 0; Conj N 264,437 / 0. |
| CN1, d ≥ 3, both orientations | `stats.py`, `sepfar` | 5,496 = 10,992/2 ordered (76 + 10,916). |
| SF | `dl -m sepfar` | 10,916/0 at order 9; 76/0 at order ≤ 7. |
| CN1 joint | `dl -m both` (order 9, about 17 min) | cn1 = 9,617, noboth = 328. |
| CN1 joint, leaves | `dl_cn1` variant | 0 of 5,458 CN1 pairs with d(a), d(b) ≥ 3 fail, so all 328 have a leaf. Orders 5, 7: all 27 failures have a leaf. |
| Set form N2 | `dl -m sets -k 2` | hyp2 = 675,641, 0 violations. |
| Maximal form | `dl -m nmax` | nmax 300,644 / 0; "local" 79,598 / 0 (F8). |
| §10.1 | `exp1.py oe57.g6` | inst 334, no_robust 115, ab_target_ex 334; 22 CN1 with d(g) ≥ 4 and d(a), d(b) ≥ 3. |
| §10.2 | `exp3`, `exp4`, `exp5` | 3,284 / 1,224 / 453 (76 instances); far condition: exists 76, sufficient with separation 76; 7,442 / 2,668 (169 instances). |
| §10.3 | `closure.py 5`, `closure.py 7` | STUCK 4 and 594. The four at order 5 are DCw, DEk (×2) and DTw (F2). |
| §10.4 | `dl -m sep1` | 118 instances, 0 separable. |
| Examples | `ex.py` | FsOrg: edges as stated, the child decomposition is Lovász, forced chain [6, 5], new Q(b) = 5 6 2 0 1 ∋ a, bad. DEk: Q(3) = 34 exists. FsPzw: the decomposition is Lovász and separating, Q′(g) = Q′(b), the transfer is bad. |

- **Example 10.1 by hand.** Degrees are (3,3,3,3,1,3,4), and g = 6 is the only even vertex. N(1) ∩ N(5) = {6}.
  - In G − 62 the three paths use all 9 edges, and the ends are 0,5 / 1,6 / 3,4.
  - Fan: Q′(6) = 6 5 2 0 1 contains u = 2, and the vertex before u is 5. Re-route to 5 6 2 0 1. The original path of 5, 0 3 5, avoids 2, so append: 0 3 5 2.
  - So Q(5) = Q(1) = 5 6 2 0 1, as stated.
- **DEk by hand.** (a) gives tail 0 with A = {2, 3}. In G − 03 the even vertex is 3, and N(4) ∩ A = {2, 3} ⊄ {3}, so the child is outside the class. (c) at 4 gives tail 4 with N(4) = {2} ⊆ A. (b) is empty, (d) does not apply, and (i) does not shrink A.
- **Robustness definition.** `exp1.py`'s robustness requires a good child to exist; the paper's literal definition does not. On these data the two agree: no NOROB instance has a target without a good child (`vacuous_rob.py`).

### 4.3 Independent checks (auditor)
- **Certificate soundness** (`dlrec_both`, `cert_sound.py`).
  - Orders 5–9, both orientations of all 166,998 non-twin pairs.
  - 327,634 orientations certified (164,815 S_b, 162,819 S_a). **0 of them are contradicted by the exact solver.**
  - The code rejects c ∈ A, so A25-F1 (Thm 3.1 false for c ∈ A) does not apply.
  - `MV_TR` is 0, so no move conditional on TR is used.
  - moves.h differs from the A25-audited version only in an unused constant.
  - Moves (b) and (c) with c ∈ N(g) are proved on paper in L1I Thm 3.1. (b) is also covered in Lean by `csys_caseI`; (c) with c ∈ N(g) is not in Lean. The manuscript says "proved transfers", which is accurate on paper.
- **Brute force on graphs not in the paper's set.**
  - All graphs of order 6 (disconnected and all-odd included): 146 pairs, 0 mismatches.
  - `geng 7 0:9` and `geng 8 0:9`: 1,623 pairs, 0 mismatches.
  - On these the failures are exactly the twins (27 = 27).
- **Solver logic (read).**
  - `decomposable` enumerates every path from the smallest-degree odd vertex to another odd vertex. That is complete for the profile b = d mod 2.
  - The Lovász shortcut and the counting shortcut are valid.
  - Budget-hit results are never memoised. The final call of `avoid` is unbudgeted, so it is exact.
  - The `sepfar` and `sep1` modes disable the Lovász shortcut and reset the memo around each query.

## 5. Findings

**F1 (ERROR; §10.4, l. 541–543).**
- **Claim.** "The reason is local: a vertex of degree two adjacent to a and b (or to b and the common neighbour) forces a path through both."
- **What the data show.** Only **14 of the 118** instances have such a vertex. In **72 of the 118**, d(g) ≥ 4, so G has no vertex of degree two at all: g is the only even vertex, and the graph is connected.
- **Example.** FsPIW (edges 01, 02, 03, 14, 15, 16, 45, 46, 56; g = 1, a = 0, b = 4, degrees 3,4,1,1,3,3,3). Full enumeration gives 18 decompositions, none separating, and no degree-two vertex exists.
- **Fix.** Delete the sentence, or replace it with an accurate description. The 118 count itself is right, and so is the conclusion that separation is the wrong strengthening.

**F2 (ERROR, minor; §10.3, l. 533).**
- **Claim.** "The smallest is DEk."
- **Counterexample.** `closure.py 5` itself lists **DCw**: edges 03, 04, 14, 24; g = 0, c = 4, A = {3}, witness w = 1. It is stuck under (a)–(d), (i) and has 4 edges; DEk has 5.
  - (a) leads to tail 0, whose only neighbour 3 lies in A.
  - (b) and (c) are empty, and (i) does not shrink A.
  - DCw is good: Q(4) = 24 in {1 4 0 3, 2 4}.
- **Fix.** Present DCw, or write "one of the four order-5 instances is DEk". E31 says "(`DEk`)", which is fine.

**F3 (GAP / OVERCLAIM; §12 item 1 l. 586; README Status "d(g) ≥ 4").**
- **Claim.** "DL(1) in the core with d(g) ≥ 4" is listed as what remains.
- **What is missing.** The core with **d(g) = 2 and a common neighbour other than g** is not proved. Cor 7.2(3) lists exactly this case. Cor 6.2 needs g to be the only common neighbour, and Prop 7.1 has no target, since N(g) = {a, b}.
- **Data.** 1,108 of the 1,430 non-twin core pairs with d(g) = 2 to order 9 are of this kind. All satisfy DL(1) computationally.
- **Fix.** Add "and d(g) = 2 with a second common neighbour of a, b" to §12 and to the README.

**F4 (OVERCLAIM; §10.5 l. 547–548; abstract "The open core"; README).**
- **Claim.** "The open configuration is the core: a, b ∈ N(g), …, d(a), d(b) ≥ 3, and every neighbour of g adjacent to a or b (Corollary 7.2)."
- **Problem.** Cor 7.2 does not give a, b ∈ N(g), nor d(a), d(b) ≥ 3 off N(g).
- **What else is open.** A smallest counterexample may have a ∉ N(g) or b ∉ N(g). There DL(1) follows only from L1*, which is open, as "What was known" says.
- **Wording.** "With a common neighbour" is redundant once a, b ∈ N(g), since g is one.
- **Fix.**
  - Write "Modulo L1* (which gives S_b when a ∉ N(g) and S_a when b ∉ N(g)), the open configuration is …", and drop the Cor 7.2 citation for a, b ∈ N(g).
  - In the abstract, write "the core, a, b ∈ N(g)".

**F5 (OVERCLAIM; title l. 30; abstract l. 58; Results item 6 l. 136; §8 l. 405 and l. 414; README "Verified … 11").**
- **Title.** It says "the exact boundary to order eleven", but the order-11 row is pending.
- **Rendered abstract.** It reads "connected graph of order 5, 7, 9 pending".
- **Four slices.** "On four slices of order 11 (*pending*) every non-twin pair is certified" asserts a result. There is no order-11 certificate or slice output anywhere in the repository.
- **README.** It lists order 11 under "Verified by computation".
- **E31.** Its order-11 row points to "the update line below", which does not exist.
- **Fix.**
  - Until the data are committed, the title should say "to order nine".
  - Delete or hedge every order-11 sentence and the README entry.
  - When the data arrive, commit the slice summaries and the `dlrec` outputs for the four slices, with their indices.

**F6 (OVERCLAIM; Status l. 144; abstract l. 47–49).**
- **Claim.** "Proved means: … for items 1–5, also in Lean".
- **What §11 itself says.** The following are not formalised:
  - the component form of item 1;
  - item 5's non-twin claim;
  - Cor 7.2;
  - Cor 6.2's second part.
- **Abstract.** It lists "universal twins lie on every path of every Lovász decomposition" under "Proved and formalised in Lean" without "(connected form)".
- **Fix.** "For items 2–4, for the connected form of item 1 and for the transfer of item 5, also in Lean". Add "(connected G)" in the abstract.

**F7 (MINOR, Lean against paper; Prop 7.1 l. 326 vs `disjL1_free_target`).**
- **Mismatch.** The paper says "so does G, with the same disjunct". The Lean conclusion is only `TriangleDisj D [(a,b)]`.
- **Lean proof.** It does keep the disjunct, branch by branch.
- **Fix.** Strengthen the Lean statement: return `(S_b of D′ → S_b of D) ∧ (S_a of D′ → S_a of D)`, or state the two orientations separately via `csys_caseI`. Otherwise mark "same disjunct" as paper only.

**F8 (GAP, data; §9 l. 443–444; `dl.c` l. 452).**
- **Claim.** "with w = g this would be the local form of L1*, which held in 79,598 further queries".
- **What the code tests.** For w = g, `nmax` executes `if (w == g) Am &= ~(1u << g);`. That allows g on Q(y), so it tests V(Q(y)) ⊆ N[y] ∪ N[g]. L1S Conjecture 1.4 requires V(Q_c) ⊆ N[c] ∪ N(g), so Q_c must avoid g when g ∉ N(c).
- **Corrected run.** With g kept in the avoided set (auditor variant `dl_loc`), the true local form holds in **86,882** order-9 queries with 0 violations. The count is larger because sets A = {g} are no longer skipped as empty.
- **Fix.** Correct the code and the number, or describe the tested statement.

**F9 (MINOR, data wording; §8 l. 378–381).**
- **"942 pairs".** It means "942 of the 968 pairs". 26 pairs in 8 graphs exceed `brute.py`'s cap of 3·10⁶ transition systems.
- **The 2,204-pair set.** "Sparse graphs of orders 7, 8" is not specified, and there is no command.
- **The 129-graph enum comparison.** No command either.
- **Fix.** Say "942 of 968". Give the generator and commands, for example `geng 7 0:9`.

**F10 (MINOR, reproducibility; §8 Structure, §10.4).**
- **Unscripted numbers.** No committed script computes 6,221 / 5,648 / 85,139 / 264,437, or the 118 of §10.4 from `sep1` output. The README has no command for them.
- **Status.** All of them reproduce: `A29-scripts/stats.py` on `dl -m pairs` output, and `sep1` + `sep1_reason.py`.
- **Fix.** Commit an analysis script (`stats.py` may be adopted) and README lines.

**F11 (MINOR, statement hygiene).**
- **Conj 9.3 (CN1) and 9.4 (SF).** Both omit "a, b non-adjacent" (and "g the only even vertex"). As written, both are false for adjacent a, b.
  - **Counterexample.** The triangle g a b with one pendant edge at a and one at b. Then d(g) = 2, d(a) = d(b) = 3, and g is the only common neighbour.
  - For SF, ab lies on a path of every decomposition of G − ga.
  - For CN1, I enumerated all four Lovász decompositions of G (`enum.c`). None has both a ∉ Q(b) and b ∉ Q(a):
    - in two of them Q(a) = Q(b) (a g b, and a b);
    - in the other two Q(a) ∋ b and Q(b) ∋ a (a g b ℓ_b with b a ℓ_a, and a b ℓ_b with b g a ℓ_a).
- **Thm 5.1.** It says "at most one even vertex g" but needs g even (the proof uses d_H(g) = d(g) − 1 odd; the Lean has `hg`). Write "exactly one even vertex g".
- **Fix.** Add "non-adjacent" to Conjectures 9.3 and 9.4, and "exactly one even vertex g" to Thm 5.1.

**F12 (MINOR; Cor 7.2 l. 343–357).**
- **Problem.** Minimising |E(G)| does not remove isolated vertices, so "G is connected" does not follow.
- **Fix.** Write "G has exactly one non-trivial component", or minimise |V| + |E|.

**F13 (MINOR, abstract).**
- **Lemma NP bullet.** "In a graph with all degrees odd, two adjacent vertices need not be the two ends of one path" is false when their component is a single edge (Remark 4.3). Add "unless their component is a single edge (d(x) ≥ 3)".
- **"Structure in the data" bullet.** It states universals: "fails only if …"; "both orientations hold, and indeed in one decomposition". Add the range: order ≤ 9, and order 9 for the joint form. The auditor's runs add orders 5 and 7 for the joint form.

**F14 (MINOR; abstract "minimal counterexamples", Results item 7, E31 "Smallest: FsOrg").**
- **FsOrg.** It has minimum order (7), but not minimum size among the 22 no-robust CN1 pairs with d(g) ≥ 4: **FqGV_** has 9 edges, FsOrg has 10.
- **FsPzw.** It has 13 edges; FqhPw, FsXPw and FsZPo, among the 54 unrepaired instances, have 11.
- **DEk.** See F2.
- **Fix.** Say "an example of minimum order", or use the smallest.

**F15 (MINOR; §10.2 l. 519–530).**
- **Different populations.** "Bad in 1,224 of 3,284" comes from 76 ordered CN1 pairs with d(a), d(b) ≥ 3 (exp3). "Does not rescue 2,668 of 7,442" comes from 169 CN1 pairs with only d(a) ≥ 3 (exp5). The text does not say this.
- **Missing proof.** "Fails exactly when the chain stops at β" is stated without proof; the two-line proof is in §2.5 above.
- **Fix.** Name both populations and add the proof.

**F16 (MINOR, exposition).**
- **Prop 9.5.** It needs "a path of D′ with no end at a chain vertex is unchanged". That is a property of the chain (RD Lemma 2.2, CLT `Tracks`), not of Lemma 2.1 as worded, which only gives V(Q(b)) ⊆ V(Q′(b)) ∪ {a}.
- **§10.1.** It invokes Prop 7.1 for targets adjacent to one of a, b. The twin argument extends to them (§2.4), but Prop 7.1 does not state it.
- **Fix.** Add the unchanged-path clause to Lemma 2.1. Add "(the same argument covers targets adjacent to at most one of a, b)" to Prop 7.1.

**F17 (MINOR, cross-references and wording).**
- Cor 6.2's "More generally" introduces a case disjoint from the first part, not a generalisation. Write "Also".
- README "the strategy experiments of manuscript §9" should be §10.
- The brief's numbers (8.2, §10 table) are those of an earlier draft; see the numbering note above.
- The Prop 7.1 proof says "d(a) = |C′| − 2 is odd"; it means "is even, but a is odd".

**F18 (MINOR; §8 l. 410–411).**
- **Base case wording.** "No even vertex and d(c) = 1" omits "and the neighbour of c is not in A". `moves.h` checks this, and the base case is false without it.
- **Fix.** Add the clause.

## 6. Overall verdict

**Mathematics: SOUND.**
- The proved cases are correct as stated, apart from implicit hypotheses (F11, F12): the exception, Lemma NP, leaf at g, d(g) = 2 with g the only common neighbour, the second part of Cor 6.2, free targets with a non-twin child, the smallest-counterexample structure, the near-twin reduction under N, and SF ⇒ DL(1) on CN1.

**Lean: SOUND and faithful.**
- It builds, has no `sorry`, and uses only the three standard axioms.
- One conclusion is weaker than the paper (F7).

**Computations: SOUND and reproducible.**
- Every number I re-ran matches exactly, and the certificate calculus passed an independent soundness check.
- One explanatory sentence is false (F1), one "smallest" is false (F2), and one count tests a weaker statement than named (F8).

**Framing: needs correction before circulation.**
- The order-11 claims in the title, abstract, §8 and README (F5).
- The description of what remains open: the d(g) = 2 core with a second common neighbour, and the L1*-dependent region (F3, F4).
- The extent of the formalisation (F6).

With F1–F8 fixed, the note is an accurate record of four proved cases, a conditional reduction (SF ⇒ DL(1) on CN1), and exhaustive evidence to order 9. DL(1) itself remains open, as the note says.

## 7. Author response (applied after the audit)

All findings F1–F18 are applied in `dl-one.tex`, the README and E31.
- F1: §10.4 now says that 14 of the 118 have a degree-two reason and 72 have no degree-two vertex (`FsPIW`). `sep1_reason.py` is committed in `scripts/`.
- F2: `DCw` is named as the smallest stuck instance in §10.3; `DEk` is kept as a second example.
- F3, F4: the abstract, §10.5, §12 and the README name both open regions: the d(g) = 2 core with a second common neighbour (1,108 pairs), and the region that depends on L1*.
- F5: order 11 is complete: 11,959,367 graphs, 268,990,425 pairs, 12,516 failures, all of them twins (`data/n11_slices.txt`). The certificate claim now covers two slices with data, 17 and 517 (`data/n11_certificates.txt`), not four.
- F6: the status paragraph says that items 2–4, the connected form of item 1 and the transfer of item 5 are in Lean.
- F7: `avoid_free_target` is in Lean (one orientation carried across a free target). `disjL1_free_target` is derived from it with the same disjunct. The build is green and the axioms are standard.
- F8: `dl.c -m nmax` keeps g in the avoided set, which gives the true local form: 86,882 queries, 0 violations.
- F9–F18: applied as worded in §5 above. These cover the validation counts and commands, `stats.py`, "non-adjacent" in Conj 9.3/9.4, "exactly one even vertex" in Thm 5.1, one non-trivial component in Cor 7.2, the abstract's NP hypothesis and data ranges, "of minimum order", the §10.2 populations and the proof of "fails iff the chain stops at β", the unchanged-path clause of Lemma 2.1, the extension of Prop 7.1, and the wording fixes.
