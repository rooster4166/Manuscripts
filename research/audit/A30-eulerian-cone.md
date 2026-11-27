# A30 — Audit of eulerian-cone (manuscript, `EulerianCone.lean`, `CycleInsert.lean`, scripts, data)

Date: 2026-11-27. Referee stance: adversarial. Grades: **SOUND**, **GAP** (fixable), **ERROR** (false as stated), **UNCLEAR**, **OVERCLAIM** (true content, overstated).

**Version.** Audited at **e722218** (`eulerian-cone.tex`, 665 lines, md5 `bee31c84…`; pdf from the same commit). The tex changed during the audit: the working copy first read had 654 lines and no `CycleInsert.lean`. The committed version adds the Lean pointers for Lemma 5.2 / Prop 5.3, the Lean remark at the end of the proof of Lemma 5.2, and the order-10 data-check bullet. Sections 2–4 are unchanged (checked). Everything below refers to e722218.

**Line numbers.** "l." is `eulerian-cone.tex` at e722218. Numbering follows the compiled PDF (Prop 2.1–2.5, Cor 2.6, Lemmas 3.1–3.2, Thm 3.3, Prop 4.1, Ex 4.2, Lemma 5.1–5.2, Props 5.3–5.6, Thm 5.7, Remark 5.8, Conj 7.1, Remark 7.2).

**Auditor files** (`research/audit/A30-scripts/`; scratch outputs in `/tmp/claude-0`, not committed):
- `runs.sh`: every command the auditor ran.
- `recount.py`: own CB implementation, plus RE*, UC and 2-connectivity counts from the shipped `*.tab.gz`.
- `examples.py`: Example 4.2, the five "full CB" roots, `GCXnbW`, K_{2,10}, and an order-12 graph with m = 45 (F1).
- `mcut_check.py`: independent matching-cut counts.
- `structure_check.py`: structural claims of §5 on all connected Eulerian graphs of order 4–10.
- `verify_uc.py`: verifier for `re.c -u` lines with witnesses.
- `ucfail_roots.txt`: the 6 UC failures, input for the CP-SAT re-decision.
- `axioms.lean`: `#print axioms` and signature checks.

---

## 0. Headline

1. **The mathematics of §2–§5 is correct.** I checked every proof by hand. Both cases of the cycle insertion Lemma 5.2 are right, and so is every construction in Prop 5.4. All the smaller graphs in Thm 5.7 are connected, Eulerian, simple, of order ≥ 3 (or trivial and unused), and smaller in |V| + |E|. I found no false step in any lemma, proposition or theorem proof.
2. **One false sentence (F1, ERROR).** §6.3, l. 579–581: "the dense family … contains every graph of that order whose edge bound ⌈m/11⌉ is at least 5". This is false at m = 45, since ⌈45/11⌉ = 5. There are **134,770** 2-connected Eulerian graphs of order 12 with m = 45, more than the whole family of 124,004; one is `KHjrhx^J}m|~`. The auditor ran this slice with witnesses (§4.3): RE and UC hold at all 1,617,240 roots, 3 of them settled by CP-SAT. So the fix is cheap.
3. **One gap in a remark (F2).** The first "free insertion" of Remark 5.8 moves two ends from a to v. It fails when a = r and e_{D'}(r) = 2.
4. **The Lean is faithful.** It builds, there is no `sorry`, and every headline theorem uses only `propext`, `Classical.choice` and `Quot.sound`. `RootedDecomp` agrees with RE on RE's domain. The universe and instance set-up of `rootedDecomp_of_spineTestsNMC` is correct. There are two pointer-level discrepancies: Lemma 3.1 cites a threshold theorem for an equality (F4), and Cor 2.6(i) says "exactly", but Lean proves one direction (F5).
5. **Every number I checked reproduces.** I recomputed Tables 1–2, the tight-root split, the matching-cut counts, the brute-force validation, the reduction counts (orders 4–8) and the 8 uncertified roots. The provenance claims are stronger than the pipeline (F3):
   - the order-12 UC positives were produced without witnesses (`-q -m`);
   - the order-10 witnesses for the 8 budget roots are not produced by `run_all.sh`;
   - the per-root tables for the dense order-12 family and for 4-regular order 14 are not shipped.

   I re-ran all three with verified witnesses. All 1,488,048 dense roots and all 1,233,764 4-regular order-14 roots pass.
6. **The proved, computed and conjectured layers are mostly kept apart.** The exceptions are Thm 5.7(d), which is computation inside a theorem, and Thm 3.3(d) and (g), whose caveats (an unrefereed preprint; a restatement) appear only in the proof. The abstract also calls the floor-bound theorems "published" (F7, F8).

## 1. Graded items

### §2 Cones and the spine

| Item | Grade | Notes |
|---|---|---|
| Prop 2.1 (degrees, parity) | SOUND | Lean `fullCone_degree_none/some`, `fullCone_onlyEven_iff` state exactly this. |
| Prop 2.2 (J 3-conn ⇔ B 2-conn) | SOUND | Both directions checked; the order conditions (n ≥ 3, \|J\| ≥ 4) are handled. Lean `kConnected_three_fullCone_iff` matches; `KConnected k` = (≥ k+1 vertices, deleting < k vertices leaves a connected graph). |
| Prop 2.3 (T1 at a cone root ⇔ decomposition) | SOUND; wording GAP | Lean `test1At_fullCone_iff` is about `Test1At`, the conclusion of (T1) without the parity hypothesis. Read with the hypothesis (as (T1) is defined at l. 79), the per-root "iff" is false for non-Eulerian or odd B, where the left side is vacuous (F6). The second sentence (`test1_fullCone_iff`) is exact. |
| Prop 2.4 (other tests vacuous) | SOUND | All three handshake arguments checked; Lean matches. |
| Remark after 2.4 (odd n: T2 at a ∈ W genuine) | SOUND | It concerns B with exactly two odd vertices, which are adjacent. |
| Prop 2.5 (matching cuts) | SOUND | `HasMatchingCut` = every vertex has ≤ 1 neighbour across, the standard notion. |
| Cor 2.6(i) | SOUND content; OVERCLAIM wording | F5: "the cone instances … are exactly RE" holds at the apex and for even n. Lean proves only SpineTestsNMC ⇒ RE. The converse is `fullConeTests_iff`, without the NMC restriction. |
| Cor 2.6(ii) | SOUND | `rootedDecomp_of_gallai` (connected, d(r) > 0) matches. The last implication is trivial (p ≤ p_r), and it is not in Lean; nothing claims it is. |
| Matching-cut counts 0, 5, 130, 27,933 | SOUND | Recomputed by an independent brute force over bipartitions (`mcut_check.py`). K_{2,6} has no matching cut (checked by hand). |

### §3 Leaf, double, literature

| Item | Grade | Notes |
|---|---|---|
| Lemma 3.1 (p_r(B) = p(B^r)) | SOUND; Lean pointer imprecise | F4. "Even" is not needed for the equality, only d_B(r) > 0. Lean proves `RootedDecomp B r ↔ p(B^r) ≤ \|B\|/2`, the threshold form at k = \|B\|/2. |
| Lemma 3.2 (2p(B^r) ≤ p(B⊕B)+1) | SOUND | Exactly one path uses the bridge. Cutting it gives two leaf-graph decompositions of total size \|D\|+1. Lean `two_mul_pathNumber_addLeaf_le` and `rootedDecomp_of_dbl` match. |
| Thm 3.3, closure arguments | SOUND | B^r is connected, has odd order \|B\|+1 and a leaf, so it is none of K3, K5⁻, K5. It is not a SET graph: ℓ's only neighbour r is odd in B^r, so ℓ has no even neighbour. Adding a leaf preserves planarity, tw ≤ 3, 2-degeneracy and K5-minor-freeness. EV(B^r) = B − r. (e): the double is connected with Δ = max(Δ(B), d(r)+1) ≤ 5 and has even order 2\|B\|, so BP's ceiling gives \|B\|. |
| Thm 3.3, citations vs survey | SOUND (nits) | (a) BBB Thm 1.2, (b) BSCL Thm 3.2, (c) AB Thm 1, (d) ZLH Thm 1.1, (e) BP Thm 1.3 and (g) the BS Thm 2(b) restatement all match the survey's verbatim quotes, exception lists included. Nits: (f) omits "connected simple", and the SET paraphrase at l. 256 says "two" instead of "at least two" even neighbours and omits "EV(G) is a triangle" (F9). |
| Thm 3.3, access caveats | OVERCLAIM (placement) | F7. ZLH is an unrefereed arXiv v1 of 14 Nov 2026, and Pyber is restatement-based. Both caveats appear in the proof only, not in the statement, the abstract ("Published floor-bound theorems") or the intro table. |
| "cone over K_{2,6} … covered by (a) and by (g)" | SOUND | (g) covers the two degree-6 roots, which are the ones that defeat the lifts (B − r = K_{1,6}). It does not cover the degree-2 roots, but those are not the ones that matter. |
| l. 82–83 citation for the three lifts | Pointer | direct-test1 Ex 4.7 shows only the forest base (and the absence of triangle data). The forest-through-r failure is in synthesis §25 addendum (F9). |
| FHZ / Xie paragraph | SOUND | Matches the survey (FHZ: abstract plus Xie's verbatim restatement). Eulerian + 2-connected gives a cycle (FHZ), or an edge xy with all other degrees 2 (Xie). |
| BS Lemma 10 | Nit | It is stated for ESET graphs, of which SET graphs are type (i) (F9). |
| Chu–Wang "prove 3n/5" (l. 291) | OVERCLAIM (mild) | Their Thm 1.3 needs triangles pairwise at distance ≥ 3, and Thm 1.4 needs a triangle removal set (F9). |

### §4 Counting bound

| Item | Grade | Notes |
|---|---|---|
| Prop 4.1 | SOUND | v lies on (d_v+e_v)/2 ≤ p paths, so e_v ≤ 2p − d_v. Evenness comes from (1). The converse holds since the c_v are even, c_r ≥ 2 and p ≥ 2, so the e_v can be raised in steps of 2. |
| Three classical bounds | SOUND | |
| Example 4.2 | SOUND | `GTm~vs` is K8 minus the double star (s = 1 with leaves 0, 2, 3, 4; t = 5 with leaves 6, 7) and is 2-connected. CB = 4 at all roots; the classical bounds give 3 at s and t; the Hamiltonian-path argument is correct. These are exactly the 2 "full CB" tight roots at order 8 (data). |
| "CB ≤ n/2 always" (l. 593) | SOUND | For even n and δ ≥ 2: d_v ≤ n − 2, so c_v(n/2) ≥ 2 and Σc_v ≥ 2n. |

### §5 Reductions

| Item | Grade | Notes |
|---|---|---|
| Lemma 5.1 | SOUND | |
| Lemma 5.2, Case 1 | SOUND | Only one old c_j can lie on Q, and Q is oriented so that c_j ∉ Q1. Q1 a c1…cl is a path (the c_i are distinct and avoid Q1), and cl a Q2 is a path (cl is new). Ends: Q's two ends are kept, a stays interior, cl gets 2, c_j is interior. |
| Lemma 5.2, Case 2 | SOUND | cl a P' and cl…c1 a. The end at a moves to cl, and the new path returns one to a. Net: e(a) unchanged, e(cl) = 2, c_j interior. All of C is used once in both cases. |
| Lemma 5.2, Lean | SOUND | `PathDecomp.cycle_insert` proves a slightly more general statement: "∉ V(G')" becomes "no edge in G'". l ≥ 2 is automatic since s(c,a) ∉ R.edges. Case 2 is used whenever a is an end. The conclusion `ends w = ends' w + 2[w = c]` is the manuscript's three bullets, since new vertices have no D'-ends. `ear_insert` matches Prop 5.3's step. |
| Prop 5.3 | SOUND | B' is connected and Eulerian with n − 1 ≥ 3 vertices; C = a b v a with c1 = b the one old vertex. Odd n: ⌈(n−1)/2⌉ + 1 = ⌈n/2⌉. |
| Prop 5.4, component claims | SOUND | B − v is connected (reroute through ab). Deleting one edge leaves ≤ 2 components, with a and b separated. Degrees drop by 2 at a and b only. A connected Eulerian graph has order ≠ 2. Checked on all 2,108 ear-at-cut instances of order 4–10 (`structure_check.py`). |
| Prop 5.4(i) | SOUND | Both sub-cases were checked edge by edge. Interior case: Q1 a v b and P_b' b a Q2. End case: P_b' b a P_a' and a v b. The outputs are paths because V(B_a) ∩ V(B_b) = ∅ and v is new. The count is \|D_a\| + \|D_b\|, and every old end count is unchanged, b's and r's included (also when r = a). |
| Prop 5.4(ii), (iii) | SOUND | (ii): C = a b v a with b, v ∉ V(B_a). (iii): C = b v a b with c_l = a = r, and \|B_b\| = n − 2 ≥ 3 since n ≥ 4. (iii) only needs p(B_b) + 1. |
| Prop 5.4, parity bounds | SOUND | n = \|B_a\| + \|B_b\| + 1. The three parity cases give equality, equality, and (n−1)/2 ≤ (n+1)/2. |
| Prop 5.5 | SOUND | ab ∉ E: suppress u. ab ∈ E: B'' is connected (reroute), Eulerian, and has ≥ 3 vertices (d(a) ≥ 4). C = a u b v a with c2 = b. Checked on 1,908 twin instances with ab ∈ E. |
| Prop 5.6 | SOUND | Both cases. p(B/r) ≤ p_x(B/r) ≤ (n−1)/2 by RE* at any root. |
| Thm 5.7(a)–(c) | SOUND | Smaller graphs used: B/v, B_a, B_b (≥ 3 vertices in each case used), B'' or B/u, B', B/r, B − r − ab. All are subgraphs, or (for B/v, B/r) have one vertex and one edge fewer. All are connected, Eulerian and simple (ab ∉ E for suppression), with ≥ 3 vertices. The trivial components are never fed to RE*. |
| Thm 5.7(d) | SOUND as computation; labelling | F8: a computational statement inside a theorem that the intro table labels "proved, data-checked". |
| Remark 5.8, first bullet | **GAP** | F2. |
| Remark 5.8, second bullet | SOUND | |
| Remark 5.8, data (56 of 1,225) | SOUND | 1,169 + 56 = 1,225 in `reductions_check_le9.txt`. The phrase "the bound n/2+1 is actually needed" is confusing (F10). |
| Remark 5.8, "Remark 7.2 gives another formulation of the hard case" | UNCLEAR | F10. |
| Data-check paragraph, numbers | SOUND | Reproduced exactly for orders 4–8 with a fresh binary. The log counters are cumulative across files, so the order-9 line holds the totals, as the text uses them. |
| Data-check paragraph, "verifies … ends at every old vertex" | OVERCLAIM (mild) | F13. |

### §6 Computation

| Item | Grade | Notes |
|---|---|---|
| Solver description | SOUND | Code read. The odd-vertex and lowest-edge branchings are complete, the component split is exact (least s for the first component), and the memo keys are exact edge masks. The memo stores failures only when not aborted, and solve(R, ·) is monotone. The per-component pruning bound is exactly as stated. The root start bound (d_r + 2)/2 is not mentioned, but it is valid. |
| Brute-force validation | SOUND | Re-run: 473 graphs, 3,622 values, 0 mismatches. The auditor added bf.py on the 102 connected Eulerian graphs of order ≤ 8 with ≤ 13 edges against the shipped tables: 753 roots, 0 mismatches. |
| "Every positive answer comes with a witness … verified" | OVERCLAIM | F3. |
| Lower bounds: CB or CP-SAT | SOUND for Table 1; incomplete | 219/219 CP-SAT agree (log). The 6 UC failures of §7 are lower-bound claims not covered (F14). The auditor's CP-SAT run on them: 6/6 agree. |
| Generation counts 1, 1, 4, 8, 37, 184, 1782, 31026 | SOUND | Regenerated, and equal to OEIS A003049. 2-connected even orders: 1, 7, 162, 30,054 (recounted). |
| Table 1 | SOUND | `summary.py` plus the auditor's `recount.py` (own CB). n = 10: 300,320 certified with p = CB, plus 8 budget roots resolved → 300,328. Tight: 14,149 + 7 = 14,156. p > CB: 212. |
| 8 budget roots | SOUND; not reproducible from `run_all.sh` | Auditor: `re -d -r` gives verified 5-path witnesses at all 8. An unbudgeted run gives p_r = 4 at `ITzvn^nzw` r = 4 (CB = 4) (F3). |
| Tight split 14,131 / 20 / 5 | SOUND | 14,129 certified with d(r) = n − 2, plus `I]zn^^nzw` roots 0, 1 (d = 8). The five listed roots have classical bound 4 and CB 5, with m = 35, 36. Order 8: `GTm~vs` roots 1, 5. |
| RE* at 17,844 + 9,720 roots | SOUND | Recounted by order (3: 3, 4: 4, 5: 20, 6: 48, 7: 259, 8: 1,472, 9: 16,038). |
| Table 2 counts | SOUND | Every input is 2-connected Eulerian. The counts match the inputs (1,542; 7,849; 94; 1; 540; 58; 2,100 × 3), and the roots are n × graphs. All shipped tables have status OK with p ≤ k. Dense 12: regenerated (124,004 exactly). |
| Table 2, dense 12 RE and UC | SOUND (auditor re-run) | The tables are not shipped. Auditor: `re -u` with witnesses at all 1,488,048 roots, verified. 1,488,019 are UC by re.c; the other 29 are the budget roots of `uc12_unk.txt`, whose CP-SAT witnesses verify with CB = 5. |
| Table 2, 4-regular order 14 | SOUND (auditor re-run) | The table is not shipped. Auditor: `re -d` with witnesses at all 1,233,764 roots, verified. |
| Random family | SOUND; nit | "2,100 each" can include isomorphic repeats: rand_12 has only 2,036 distinct WL hashes (F12). |
| l. 579–581 "contains every graph … ⌈m/11⌉ ≥ 5" | **ERROR** | F1. |
| K_{2,10} tight at its two big roots | SOUND | CB = 6 = n/2. |

### §7 UC and Remark 7.2

| Item | Grade | Notes |
|---|---|---|
| UC statement and "strengthens RE" | SOUND (conjecture, clearly labelled) | |
| BP Question 1.1 analogy | SOUND | Matches the survey's quote. CB is 2 for K3 and 3 for K5. |
| Evidence: UC at all 2-connected roots, orders 3–10 | SOUND | Recounted from the tables, the 8 budget roots included. |
| 6 failures (1 at order 8, 5 at order 10) | SOUND | Recounted. All 6 confirmed by CP-SAT (p − 1 infeasible). |
| `GCXnbW` description | SOUND | The cut vertex is 6, with blocks {1,2,4,5,6,7} and the triangle {0,3,6}. p_r = 4 and CB = 3. |
| Remark 7.2, three bullets | SOUND | With exactly n/2 paths and d(r) = n − 2, (d+e)/2 ≤ n/2 forces e_r = 2, and all n/2 paths meet r. B − r has the single even vertex s. Pieces: one per edge rx. |
| Remark 7.2, equivalence | SOUND; wording | Forward: every edge of B − r lies on a path through r, so the pieces partition E(B − r), and the two halves of a path through r are vertex-disjoint. Converse: concatenation through r is a path when the pair is vertex-disjoint and r ∉ B − r, and the count is (n/2 − 2) + 2. "Attached at x" must mean "with an end at x", and trivial pieces are not paths (F11). |
| "99.8%" | SOUND | 14,131 / 14,156 = 99.82%. |

### Lean

| Item | Grade | Notes |
|---|---|---|
| Build, `sorry`, axioms | SOUND | `lake env lean axioms.lean` against the built library. These depend only on propext, Classical.choice and Quot.sound: `rootedDecomp_of_spineTestsNMC`, `test1_fullCone_iff`, `rootedDecomp_of_gallai`, `fullConeTests_iff`, `kConnected_three_fullCone_iff`, `rootedDecomp_of_dbl`, `PathDecomp.cycle_insert`, `PathDecomp.ear_insert`, `gallai_iff_spineTests'`. No `sorry` in either file. |
| `RootedDecomp` vs RE | SOUND | `∃ D, D.size ≤ card W / 2 ∧ 2 ≤ D.ends r` (checked by `Iff.rfl`). For Eulerian B of even order with d(r) > 0, e ≥ 1 ⇔ e ≥ 2 and ⌊n/2⌋ = n/2, so it is RE. Outside RE's domain (odd order, d(r) = 0) it is false or floor-valued, and it is never used there. |
| `rootedDecomp_of_spineTestsNMC`, universe and instances | SOUND | Signature: `SpineTestsNMC.{u} → ∀ {W : Type u} …`. The cone lives on `Option W : Type u`, so the same universe. The instance binders of `SpineTestsNMC` are instantiated by inference (`Option` Fintype/DecidableEq, `fullCone.decAdj`), and these are the instances `test1_fullCone_iff` uses (the term typechecks). `SpineTestsNMC` quantifies over all instances, so no generality is lost. The matching-cut hypothesis is transported by `hasMatchingCut_delVert_fullCone_iff`. |
| `GallaiConjecture`, `RootedTest`, `gallai_iff_rootedTest` | SOUND | ⌈n/2⌉ written as (card + 1)/2. The private-leaf test is exactly as in the proof of Cor 2.6(ii). |
| "`fullCone B` is `cone B univ`" (l. 106–107) | Nit | True up to `b ∈ univ` vs `True`. There is no Lean lemma, and none is needed. |

---

## 2. Findings and required fixes

- **F1 (ERROR, l. 578–581).**
  - "The dense family contains every 2-connected Eulerian graph of order 12 with at least 46 edges, so it contains every graph of that order whose edge bound ⌈m/11⌉ is at least 5 = n/2 − 1." The "so" is false: ⌈m/11⌉ ≥ 5 ⇔ m ≥ 45.
  - Order-12 Eulerian graphs with m = 45 exist (the complement has 21 edges, all degrees odd). `nauty-geng -d1 12 21:21 | oddfilter | complg` gives 134,796 such graphs, of which **134,770 are 2-connected**, for example `KHjrhx^J}m|~`.
  - **Fix.** Either extend the family to m ≥ 45 (geng range `0:21`), or reword to "every graph with ⌈m/11⌉ ≥ 5 except those with m = 45". The auditor ran the m = 45 slice (§4.3): RE and UC hold at all 1,617,240 roots, 3 of them settled by CP-SAT. So extending the family is cheap (about 1 min to generate and 1 min to solve on 4 cores). Table 2 and the abstract would then read "order 12, m ≥ 45: 258,774 graphs, 3,105,288 roots".
- **F2 (GAP, Remark 5.8, l. 475–476).**
  - The replacement "P1 a b v and P2 a v" moves *both* ends at a to v, so e(a) drops by 2.
  - a can be the root (only v ≠ r is assumed). If a = r and e_{D'}(r) = 2, the result has no end at r, and the insertion is not free for the rooted problem.
  - **Fix.** Add "and a ≠ r, or e_{D'}(a) ≥ 4", or say that the bullet keeps |D'| but transfers two ends from a to v.
- **F3 (OVERCLAIM, provenance; l. 515–516, Table 2 caption l. 573–575, l. 541–543, l. 628, l. 639–640).**
  - "Every positive answer comes with a witness, and `verify_witness.py` checks it" is not true of the pipeline.
    - The dense order-12 UC run is `re -u -q -m`: UC lines are suppressed (`-q`) and witnesses are off (`-m`).
    - The witnesses for the 8 order-10 budget roots ("RE was witnessed at each of them") are not produced by `run_all.sh`, since `re_10_min.tab` has p = −1 there.
    - `run_all.sh` does not regenerate the "unbudgeted run and CP-SAT" at `ITzvn^nzw`.
    - The reductions log records a `/tmp/claude-0/e10_head.g6` path.
  - The per-root tables for the dense family (`re_dense12_decide`, `uc12`) and for 4-regular order 14 are not in `data/out/`, although the Files section promises per-root tables.
  - The auditor re-ran all of these with witnesses, and all pass (§4). So this is a provenance fix, not a correctness issue.
  - **Fix.**
    - Drop `-m` (and `-q`) in the UC run, and pipe it through a UC-aware verifier (as in `A30-scripts/verify_uc.py`).
    - Add the decide commands for the 8 roots to `run_all.sh`.
    - Ship `re_dense12_decide.tab.gz`, `uc12.tab.gz` and `re_reg14_4.tab.gz`.
    - Fix the `/tmp` path.
- **F4 (Lean pointer, Lemma 3.1, l. 210–211).**
  - The lemma states the equality p_r(B) = p(B^r). `rootedDecomp_iff_addLeaf` proves only `RootedDecomp B r ↔ p(B^r) ≤ |B|/2`.
  - The hypothesis "d_B(r) even" is not needed for the equality (positivity suffices). It is needed in Lean only because `RootedDecomp` asks for two ends.
  - **Fix.** Either cite the general pieces (`pathNumber_addLeaf_le`, `exists_leafCost_le`, `exists_two_ends`) and say the equality is assembled on paper, or state the Lean form explicitly. Drop "even" from the paper statement or explain it.
- **F5 (OVERCLAIM wording, Cor 2.6(i), l. 180–183; abstract l. 33–36).**
  - "The cone instances of the spine, in its weakest form SpineTestsNMC, are exactly RE(B, r) …" is right only for the apex instances.
  - For odd n, the cone instances of the spine include the genuine (T2) tests at non-apex vertices (l. 165–166).
  - Lean proves only SpineTestsNMC ⇒ RE for these B. The converse is `fullConeTests_iff` (all tests, no NMC), plus the trivial transport of the NMC hypothesis.
  - **Fix.** "At the apex, the instances of SpineTestsNMC on cones over B of even order are exactly RE(B, ·) for 2-connected Eulerian B without a matching cut; Lean proves the direction SpineTestsNMC ⇒ RE (`rootedDecomp_of_spineTestsNMC`) and the unrestricted equivalence (`fullConeTests_iff`)."
- **F6 (GAP wording, Prop 2.3, l. 136–137).**
  - "(T1) holds at (J, z, r) iff B has a decomposition …" uses (T1) without its hypothesis "z is the only even vertex", which is what `Test1At` is.
  - With the hypothesis, the left side is vacuous whenever n is odd or B is not Eulerian, and the iff fails, for instance for B = a path.
  - **Fix.** Define "(T1) at (J, z, r)" as the conclusion only (`Test1At`), or add "if z is the only even vertex".
- **F7 (OVERCLAIM, literature status; abstract l. 40, intro table l. 93, Thm 3.3 statement).**
  - "Published floor-bound theorems give RE for planar graphs, …, and K5-minor-free graphs."
    - ZLH is an arXiv v1 of 14 Nov 2026, not refereed; the survey had full-text access to Sec. 1, the Sec. 2 lemmas and the final proof only.
    - BBB's full proof is the arXiv v2; only an extended abstract is published.
    - (g) rests on restatements of Pyber.
  - These caveats appear only inside the proof of Thm 3.3.
  - **Fix.** In the abstract, say "Floor-bound theorems in the literature (one an unrefereed 2026 preprint)". In Thm 3.3, mark (d) "(conditional on [ZLH], unrefereed)" and (g) "(via the restatements in [BS], [BP])". Add the same flags in the intro table.
- **F8 (proved vs computed, Thm 5.7(d), l. 452, 465–466; intro table l. 95).**
  - (d) n ≥ 11 is a computational result, proved only by exhaustive search.
  - The intro table says "proved, data-checked" for the whole row.
  - **Fix.** Label (d) "(computation, §6)" in the statement, and split the table row into "(a)–(c) proved" and "(d) computation".
- **F9 (literature nits).**
  - l. 256: a SET graph is one where "EV(G) is a triangle and every odd vertex has at least two even neighbours". The argument (ℓ has no even neighbour) is unaffected.
  - l. 269: BS Thm 13 assumes G connected and simple.
  - l. 289: BS Lemma 10 is for ESET graphs (SET graphs are type (i)).
  - l. 291: Chu–Wang prove 3n/5 under the triangle-distance ≥ 3 hypothesis (Thm 1.3), or with a triangle removal set (Thm 1.4), not for all Eulerian graphs.
  - l. 82–83: the forest-through-r failure is documented in synthesis §25 addendum, not in direct-test1 Ex 4.7, which treats the forest base and the absence of triangle data.
- **F10 (UNCLEAR, Remark 5.8, l. 480–482).**
  - "On the data the bound n/2+1 is actually needed" reads as if p_r(B) = n/2 + 1 somewhere. What is meant is that the insertion bound p_r(B') + 1 equals n/2 + 1 in 56 instances.
  - "Remark 7.2 gives another formulation of the hard case" is unclear. Remark 7.2 reformulates RE at roots of degree n − 2, which is not the even-order ear case.
  - **Fix.** Reword the first sentence. Drop the cross-reference, or explain how a minimal counterexample's hard case reduces to degree n − 2 roots (I see no such reduction).
- **F11 (wording, Remark 7.2, l. 612–616).** The equivalence is correct, but the system should be defined precisely:
  - a family (Q_x) indexed by N(r), where each Q_x is a path of B − r (possibly the trivial path x) with an end at x;
  - the nontrivial Q_x partition E(B − r);
  - the indices split into n/2 − 2 pairs {x, y} with Q_x, Q_y vertex-disjoint, plus two singletons.

  "Decomposition of B − r into n − 2 pieces" is not a decomposition in the paper's sense (§1), since pieces can be trivial.
- **F12 (nits, numbers and wording).**
  - Abstract l. 47–48: "(300,540 roots)" is the count at order 10 only; even orders 4–10 give 301,882.
  - Table 2 "random … 2,100 each": these are samples and may contain isomorphic repeats. rand_12 has only 2,036 distinct WL hashes among its 2,100 graphs, so say "2,100 samples each".
  - `run_all.sh` estimates "~1 h" for the dense UC run. The auditor's full run with witnesses took about 1 min on 4 cores (harmless).
- **F13 (OVERCLAIM, mild, data-check paragraph l. 485–487).**
  - "verifies each output independently: partition into paths, sizes, ends at every old vertex, end at r" holds only partly.
    - `reductions_check.py` checks ends at every old vertex only for EAR and TWIN.
    - SUPPRESS, EAR-CUT and the ROOT2 cases check only e(r) ≥ 1 (or = 2). That is all those claims need.
    - The ⌈n/2⌉ size assertion is made for TWIN only at even n, and for ROOT2 only at odd n.
    - The script's docstring still says "Section 6", "Lemma 6.1–6.2" and "Prop. 6.3–6.5".
  - **Fix.** State exactly what is checked, and update the docstring numbering.
- **F14 (lower-bound provenance, l. 517–520 vs §7 l. 599–603).**
  - "Every lower bound used below is either CB … or was re-decided by CP-SAT." The 6 UC failures (p_r > max(CB, ⌈n/2⌉ − 1) at cut-vertex graphs) are lower bounds from re.c's exact search only.
  - The auditor re-decided all 6 with `cpsat_check.py`: OPTIMAL at p and INFEASIBLE at p − 1, 6/6 agree.
  - **Fix.** Add these 6 to `above_cb.txt`'s CP-SAT pass, or cite this check.

## 3. Literature check (Theorem 3.3)

| Case | Manuscript statement | Survey quote (verbatim source) | Access | B^r / double in class, not exceptional |
|---|---|---|---|---|
| (a) planar | BBB Thm 1.2, except K3, K5⁻, ⌊n/2⌋ | "Every connected planar graph on n vertices, except K3 and K5⁻, can be decomposed into ⌊n/2⌋ paths." | full arXiv v2 (main file) | yes; the leaf excludes K3, K5⁻ |
| (b) tw ≤ 3 | BSCL Thm 3.2 | "connected partial 3-tree … pn ≤ ⌊n/2⌋ or G ≅ K3 or K5⁻" | full arXiv v1; the journal version's numbering is unchecked (stated) | yes |
| (c) 2-degenerate | AB Thm 1 | "… at most ⌊n/2⌋ paths unless G is a triangle" | full | yes |
| (d) K5-minor-free | ZLH Thm 1.1 | "If G is not isomorphic to K3 or K5 − e, then pn(G) ≤ ⌊\|V(G)\|/2⌋" | arXiv v1, unrefereed (stated in the proof only, F7) | yes |
| (e) Δ ≤ 4 | BP Thm 1.3 on the double | "If Δ(G) ≤ 5, then G admits a path decomposition into ⌈n/2⌉ paths." | full arXiv v1 | double connected, Δ ≤ 5, even order |
| (f) Δ(B − r) ≤ 3 | BS Thm 13 | "connected simple graph … Δ(EV(G)) ≤ 3, then either G is a Gallai graph or G is a SET graph" | full arXiv v1 | EV(B^r) = B − r; not SET |
| (g) B − r forest | Pyber via BS Thm 2(b), BP | "(b) If EV(G) is a forest, then pn(G) ≤ ⌊n/2⌋" | restatement only (stated in the proof) | EV(B^r) = B − r |

The survey's own summary table (lines 378–381 of the notes) lists the exceptions loosely ("planar, except K3", "treewidth ≤ 3, except K3", "K5-minor-free, except K3"), inconsistently with its verbatim quotes. The manuscript uses the correct verbatim lists. This is a nit about the notes only.

## 4. Computation: reproduction

### 4.1 Reproduced from shipped data or a fresh binary (gcc -O2 of `re.c` at e722218)
- `compare_bf.py`: 473 graphs, 3,622 values, 0 mismatches (exact).
- bf.py on 102 connected Eulerian graphs of order ≤ 8 with ≤ 13 edges, against `reconn_*`/`re_*_min` tables: 753 roots, 0 mismatches.
- `summary.py` and `recount.py`: every Table 1 entry, the tight split, the RE* counts by order, and the UC failures (6: `GCXnbW` r6; `I?BEHrE}O`, `` I?`@`cr~? ``, `ICdcrHd}_` at r9; `IQhTTViyg`, `IQhTVViiw` at r1).
- `reductions_check.py` on orders 4–8: identical counters.
- Matching cuts: 0, 5, 130, 27,933 (independent brute force).
- Counts of connected and 2-connected Eulerian graphs: regenerated.
- §5 structural claims on orders 4–10: 24,879 suppressible vertices, 23,026 ears with B' connected, 2,108 ears at a cut, and 1,908 + 1,995 twin pairs. No violation.

### 4.2 Re-decided by the auditor (data not shipped, or not produced by the pipeline)
- The 8 order-10 budget roots: verified witnesses of size 5, and of size 4 at `ITzvn^nzw` r = 4.
- Dense order 12, all 124,004 graphs and 1,488,048 roots, `re -u` with witnesses:
  - all verified (partition, two ends at r, size ≤ max(CB, 5));
  - 1,488,019 by re.c, plus the 29 budget roots, which match `uc12_unk.txt` in number, have CB = 5, and whose CP-SAT witnesses in `uc12_unk_cpsat.txt` verify.
- 4-regular order 14, all 1,233,764 roots, `re -d` with witnesses: all verified.
- The 6 UC failures: CP-SAT agrees (INFEASIBLE at p − 1).

### 4.3 The m = 45 slice (F1)
134,770 2-connected Eulerian graphs of order 12 with exactly 45 edges (1,617,240 roots), run with `re -u -b 2000000` and witnesses, checked by `verify_uc.py`.
- **RE holds at all 1,617,240 roots** (every witness verified).
- UC was decided and verified at 1,617,237 roots. The other 3 hit the budget: `K~~xxzFp}MFX` roots 2 and 3, and `K~|{{~fX{ukE` root 0, each with CB = 5 (`A30-scripts/m45_unk.txt`).
- At those 3, an unbudgeted `re -u -r` and CP-SAT (`cpsat_decide.py`, 900 s) both find 5-path decompositions with two ends at r, and the CP-SAT witnesses verify. So p_r = CB = 5, and **UC holds at all 1,617,240 roots**.
- So the family can be extended to m ≥ 45 (258,774 graphs) with the same result. This makes the sentence of F1 true, once these runs are put into `run_all.sh`.

## 5. Proved, computed, conjectured: placement

- **Proved on paper:** Props 2.1–2.5, Cor 2.6, Lemmas 3.1–3.2, Prop 4.1, Lemmas 5.1–5.2, Props 5.3–5.6, Thm 5.7(a)–(c), and Remark 7.2 (with F11).
- **Proved in Lean:** §2, Lemmas 3.1 (threshold form; F4) and 3.2, Lemma 5.2, and the insertion step of Prop 5.3. Not in Lean: Prop 4.1, Prop 5.4, Props 5.5–5.6, Thm 5.7 (the table row says only "insertion lemma in Lean", which is accurate).
- **From the literature:** Thm 3.3. (d) is unrefereed and (g) restatement-based (F7).
- **Computation:** Thm 5.7(d) (F8), Tables 1–2, the tight split, UC evidence, and the "RE* at all roots ≤ 10" claim.
- **Conjecture:** UC, clearly labelled.
- **Wording that blurs the layers:** "Published" (F7), "proved, data-checked" for a row containing (d) (F8), "every positive answer comes with a witness" (F3), and "every lower bound … CB or CP-SAT" (F14).

---

## 6. Author response (eulerian-cone session, after the audit)

| Finding | Disposition |
|---|---|
| F1 | **Fixed by extension.** The dense family is now every 2-connected Eulerian graph of order 12 with m ≥ 45 (complement ≤ 21 edges): 258,774 graphs, 3,105,288 roots. `re -u` was run with witnesses and checked by the new `verify_uc.py`. 3,105,256 roots satisfy UC directly; the other 32 got CP-SAT witnesses (CB = 5), all verified. The m = 45 slice ships as `data/dense12_m45_2c.g6.gz`. This agrees with the auditor's own run. The coverage sentence is now true. |
| F2 | Fixed: the first bullet now says it moves two ends from a to v and keeps an end at r only if a ≠ r or e(a) ≥ 4. |
| F3 | Fixed. The UC run is with witnesses (`verify_uc.py`). The 8 budget roots are in `run_all.sh` and shipped (`out/budget8_decide.txt`, verified), with the unbudgeted minimum and the CP-SAT check at `ITzvn^nzw`. Per-graph tables ship for the dense family and for 4-regular order 14 (`*.pg.gz`, via `compact_pg.py`). `data/SHA256SUMS` lists the inputs. The reductions log now uses a repository path. The witness claim is reworded. |
| F4 | Fixed: Lemma 3.1 now assumes only d(r) > 0; the Lean pointer says "threshold form", and the paragraph explains where evenness enters. |
| F5 | Fixed: Cor 2.6(i) is restricted to the apex and even order, states which direction Lean proves, and notes the odd-n (T2) instances. The abstract was changed to match. |
| F6 | Fixed: Prop 2.3 speaks of the conclusion of (T1) (`Test1At`). |
| F7 | Fixed: "Floor-bound theorems in the literature … one an unrefereed 2026 preprint" in the abstract. Thm 3.3 now marks (d) and (g) in the statement, and the intro table does too. |
| F8 | Fixed: Thm 5.7(d) is labelled "by computation"; the intro table gives it a separate row. |
| F9 | Fixed: the SET definition, "connected and simple" for BS Thm 13, ESET for BS Lemma 10, Chu–Wang's hypotheses, and the source for the forest-through-r failure (synthesis §25). |
| F10 | Fixed: reworded, and the cross-reference is removed. |
| F11 | Fixed: Remark 7.2 now defines the family (Q_x) precisely, with the reassembly. |
| F12 | Fixed: the abstract gives 301,882 roots, Table 2 says "2,100 samples each" with a note on repeats, and the run-time estimate is corrected. |
| F13 | Fixed: the data-check paragraph says exactly what is checked, and the docstring numbering is updated. |
| F14 | Fixed: the 6 UC failures were run through CP-SAT (`out/ucfail_cpsat.txt`, 6/6 agree) and are cited in §6. |

New after the audit, outside its scope:
- §3 adds a comparison with the project's own collection (marked-reduction §§23, 25; separating-pairs Cor 13.12). MR Cor 168 and Thm 170 were checked exactly to order 10 (`dense_check.py`).
- Remark 5.9 adds the fat theta, as an application of Thm 5.7(b).
