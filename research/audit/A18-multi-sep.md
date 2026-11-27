# A18: Referee audit of multi-sep (MSEP, CSEP, leaf merge, Case I, sparse classes)

- **Date:** 2026-11-27
- **Auditor:** fresh subagent (adversarial referee pass). I did not edit the manuscript, the Lean files or the scripts.
- **Scope:** `manuscripts/multi-sep/multi-sep.tex` on branch `claude/multi-sep`, all sections. The background results in `manuscripts/route-descent/route-descent.tex` (RD) were checked for citation form only. Also audited: the scripts and outputs in `manuscripts/multi-sep/scripts`, the log `research/experiments.md` E21, and `lean/GallaiLean/MultiSep.lean`.
- **Version audited.** The files changed while I worked:
  - The final text is commit 13d0d8f (HEAD 79592a0). Its md5 is `e81751c4…`. It differs from the first version I read only in the abstract, the Formalisation section and three citations.
  - The final Lean file has md5 `c9a0403c…` and equals HEAD.
  - At 05:27 an uncommitted version of `MultiSep.lean` contained a `sorry` in `realisable_of_separating`, which was then being written. The committed version has none.
  - Line numbers below refer to the final .tex.
- **Independent checks.** My scripts are in `research/audit/A18-scripts/`.
  - `overlap_check.py`: brute force over all end-edge choices for the counterexample in Remark 9.
  - `combined.py`: a mixed certified strategy using Case I, Case II and rotation.
  - `sqcol_check.py`: true chromatic number χ(K²) against the start value of `min_colouring`.
  - `val_dist.py`: recounts the failures in the cubsep cross-validation.

## Verdicts

| # | Item | Verdict |
|---|---|---|
| 1 | Prop. `reduction` (a), (b), (c) | SOUND |
| 2 | Prop. `cover` | SOUND |
| 3 | Lemma `merge`, Lemma `packedlift`, Thm `endedge`, Thm `caseII` | SOUND |
| 4 | Prop. `EE`, Conj. `EE`, Lemma `caseI`, Lemma `rotation` | SOUND WITH FIXES (wording only) |
| 5 | Thm `sparse`, Cor. `sparse` | SOUND WITH FIXES (Cor. has no proof; theorem understated) |
| 6 | Section `limits` | SOUND WITH FIXES (one count wrong; one experiment misdescribed) |
| 7 | Lean `MultiSep.lean` | SOUND (statements match; nits) |
| 8 | Novelty and wording | SOUND WITH FIXES |

### Details per item

**1. Proposition `reduction`.**
- (a) Each vertex of Ev loses exactly its matching edge, and the other vertices stay odd. This uses "no isolated vertices", silently.
- (b) Correct in both directions. If ca lies in a triangle caw, then cw and aw lie in F because N already covers c and a.
- (c) The path extension is correct in every case:
  - one end of Q is a tail: the head a_i is off Q by the separation hypothesis;
  - both ends are tails: i ≠ j because the ends are distinct, a_i ≠ a_j because N is a matching, and both heads are off Q;
  - tail at one end, head a_j at the other: a_i ≠ a_j because a_j ∈ Q and a_i ∉ Q.
- (c) End counts: tail 0; head 2, from two distinct paths (its own path contains a_i, while c_i's path does not); odd vertex 1. Path count |D| = n/2, and n is even by (a).

**2. Proposition `cover`.**
- Fibres are packed.
- Lifts are unique and are paths.
- Each edge vw lies on exactly one lift: lifts of the same P are vertex-disjoint, since a vertex over p_i can only sit at position i.
- Lifting gives a bijection between the end fibres, so each vertex is an end of exactly one lift.
- All of this is correct for simple L. The definition via N(v) presupposes that L is simple. The "Reformulations" paragraph speaks of multigraph quotients, which are not needed.

**3. Leaf merge, packed lift, prescribed end edge, Case II.**
- Lemma `merge`: f is a bijection on edges and injective on each V(P). The end bookkeeping is right.
- Lemma `packedlift`: correct. The cases x ∈ A, a = x and a ≠ x are all covered.
- Theorem `endedge`, degree bookkeeping:
  - d_H(x) = d_K(x) − 1 and d_H(u) = d_K(u).
  - b_D(x) = 0 + 1 = 1.
  - The case d(x) = 1 is fine: x is then isolated in H, and b_{D_H}(x) = 0.
- Theorem `endedge`, terminal edge: P_ℓ ends at ℓ with terminal edge uℓ, so f(P_ℓ) ends at x with terminal edge ux, and it is the unique path ending at x.
- Theorem `caseII`: A_H consists of packed, pairwise disjoint sets. {x, ℓ} is packed by Lemma `packedlift` applied to A = {x}. The pull-back f⁻¹(A) is exactly the corresponding class A′. The consequence (degree ≥ 3, or all degrees ≤ 1) is right.

**4. Case I material.**
- Proposition `EE`: both directions are correct.
  - (i) ⇒ (ii): z is interior to P, so R is non-empty. The rainbow property of P gives that Rz avoids A(u).
  - (ii) ⇒ (i): the appended path meets A(u) only in u.
- Lemma `caseI`: trivially correct.
- Lemma `rotation`: I checked it carefully and it is correct.
  - Q_i ≠ Q_{i±1} is forced by "Q_i avoids c_{i+1}".
  - A path with both ends c_i and c_j on C is extended at both ends by the distinct vertices c_{i+1} and c_{j+1}, both off Q.
  - Each c_i loses the end of Q_i and gains the end of the extended Q_{i−1}, and these two paths are different.
  - The class condition is exactly what is needed when both ends are extended.
- The leaf-to-leaf remark is also correct: the end counts at p_0, p_1, …, p_m check.
- The issues are in the surrounding text (findings 6, 9, 13–15).

**5. Theorem `sparse`.** All four cases, the measure ν, the transfer of the hypotheses to H(K;x,u) when x ∉ X, and Fan's condition all check.
- Case I: Z(u) = ∅ < 1.
- Case II: Z(x) = ∅ < 2, and t = u, x are non-adjacent in K − xu.
- Case IV: K is a matching.
- The case split is exhaustive.
- "Contains Theorem `sep`": correct, with 𝒜 = {X}.
- Corollary `sparse` follows from Theorem `sparse` together with (b) and (c), but no proof is written (finding 3).

**6. Section `limits`.** It is clearly labelled computational, and no proof in §§1–7 uses it. Reproduced:
- cubsep gives 54, 2,846 and 269,966 at orders 10, 12, 14;
- 36,024,731 at order 16 (37 s);
- 8,260,200 at order 18, with 0 failures;
- `validate_cubsep.py`: 285/285 agreement;
- `coarsen_fail.py 10`: 13/24;
- `randlov.py` certified all 176 undecided instances in `out/gen_pair.txt` (snapshot of 05:27);
- the order-12 overlap counterexample of Remark 9, confirmed by an independent brute force.

Problems: findings 1, 7, 8, 10, 11, 12.

**7. Lean.** `lake env lean` on the committed file finishes with 27 warnings and no errors. It has no `sorry`. `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for all of:
- `leaf_merge`
- `lovasz_endEdge_set`, `lovasz_endEdge`
- `caseII_lift`, `classSep_allOdd`
- `classSep_caseI`
- `separation_sparse`
- `realisable_of_separating`, `realisable_of_lovasz_separating`

I ran this from a copy in the scratchpad, so no file was left in the repository. Statement by statement:
- `leaf_merge` matches Lemma 11.
- `lovasz_endEdge_set` concludes "∃ P ending at x with s(x,u) ∈ P.edges". That gives the terminal edge, since P is a path.
- `caseII_lift` is slightly more general than Theorem 14: it requires neither disjointness nor the ClassFam property.
- `classSep_allOdd` is exactly the "Consequently" of Theorem 14. ClassFam and ClassSep match the class-family and CSEP definitions.
- `classSep_caseI` matches Lemma 17, in existential form.
- `SparseFam` allows any X containing the union, which is equivalent.
- No definition is vacuous: Packed, MeetsOnce, evenSet and PathDecomp with positive-length paths are all as intended.

Nits are collected in finding 17.

## Findings

1. **major — §8 "What does not work", bullet "Certified moves" (l. 527–533), and the abstract (l. 65): the tested strategy is misdescribed.**
   - **Problem.** The text says that "an induction using only Theorem caseII, Lemma caseI and Lemma rotation (exhaustive search over all choices) fails". The scripts do something else:
     - `coarsen_fail.py` searches Case I/II only.
     - `rotate.py` searches rotations only, and caps cycle and leaf-path length at `maxlen` (default 8).
     - No mixed strategy was run.
   - **The rotation figures depend on the cap.**
     - "14 of 152 at order 12" is reproduced only with `rotate.py 12 "" 2 10`, i.e. cap 10 < n.
     - With all cycle lengths (cap 12) it is 4/152 (and 5/228 with per = 3).
     - With the default cap 8 it is 23/152, and 12/24 at order 10.
     - "1 of 24 at order 10" needs a cap of at least 10.
   - **The conclusion nevertheless survives.** My mixed exhaustive search (`A18-scripts/combined.py`: Case I, Case II and rotation interleaved freely, all cycle lengths) still fails on 2 of the 13 Case-I/II failures at order 10:
     - `I?`cspoX?` with pairs (7,1)(5,3)(0,8)(9,4)(2,6);
     - `ICOef?kF?` with pairs (7,9)(6,8)(2,3)(0,4)(5,1).

     cubsep confirms that both instances are separable.
   - **Fix.** Describe the two separate searches and give the cap. Report the uncapped rotation numbers. Add the mixed-strategy result: 2 of 24 at order 10, in my run. Phrase the abstract as "computations show that the three certified moves alone do not suffice on some small instances", not "we show … cannot prove MSEP". Also soften "a proof of MSEP must use information that is not local" (l. 533).

2. **minor — Theorem `sparse` (l. 422–458), statement: the theorem is understated.**
   - **Problem.** The same induction preserves a stronger invariant: every path meets X in at most one vertex, or exactly in the two ends of an edge of K[X]. The reasons:
     - Fan targets lie outside X.
     - New single-edge paths have an end outside X.
     - The paths of Case II are sub-paths.
     - Case IV paths are edges of K[X].

     Since a packed set contains no edge, the family 𝒜 plays no role beyond its union. "Even for overlapping classes" is therefore free, and the contrast with Remark 9 is less informative than the text suggests.
   - **Fix.** State the single-set form (X with at most one X-neighbour per vertex). Derive the family version as a remark.

3. **minor — Corollary `sparse` (l. 460–470).**
   - **Problems.**
     - No proof is given.
     - The hypothesis "no edge of N in a triangle" is redundant. A triangle caw would give w two F-neighbours c, a ∈ Ev.
     - "Packed subsets of Ev" should say "packed in F".
     - "It is new as a statement about all orientations" is unhedged.
   - **Fix.** Add the two-line proof: (a), (b), then Theorem `sparse` with 𝒜 = N, then (c). Drop the redundant hypothesis or note that it is implied. Use "we have not found this in the literature".

4. **minor — the paragraph after Conjecture `EE` (l. 366–367): the claimed analogue is not a theorem.**
   - **Problem.** "Compare Theorem endedge, which is the analogue without an even vertex and is a theorem" holds only for a single packed set. The class-family analogue (all degrees odd, class family, prescribed terminal edge xu) is equivalent, via the proof of Theorem 14, to CSEP for H(K;x,u) with 𝒜_H, which is open.
   - **Fix.** Say "for one packed set (or without classes)".

5. **minor — notation: L_1 is never defined** (l. 302, 367–370, 567). Define it, or cite it as [RD, Theorem 21]: the path ending at c avoids a packed set Y with no vertex in N[c].

6. **minor — citations to RD.**
   - **Problem.** The final version replaced the correct precise citations with vaguer ones:
     - [RD, Lemma 3] became "the form proved in [RD]";
     - [RD, §8] became [RD].

     The citation "[RD, E20]" (earlier version) referred to nothing in RD. Its replacement "(project experiment E20)" (l. 371) is an internal reference. The statement in question appears in RD as Remark 25 (second bullet).
   - **Fix.** Use [RD, Lemma 3], [RD, Theorem 19], [RD, Conjecture 30, §8] and [RD, Remark 25]. These are the RD numbers in its compiled PDF. Lemma 3 and Theorem 19 are cited in exactly the form RD proves them.

7. **minor — Remark `overlap` (l. 225–229), and the disclaimer of §8 (l. 474).**
   - **Problem.** Remark 9 asserts as fact ("the statement is false") something established only by computation. It uses "rainbow", which is defined only for class families. The instance appears only in the log.
   - **Verification.** I verified the instance independently: `K??FEaKR@oE_`, 16 pairs, minimum distance 3, a union of 3 perfect pairings, and no separating Lovász decomposition among all 3¹² end-edge choices.
   - **The disclaimer.** "Nothing in Sections 1–7 depends on this section" is literally false. Remark 9, the remark after Conjecture `EE` ("we found no failure") and the remark after Lemma `caseI` ("we show in Section limits") all rely on §8.
   - **Fix.** Put the explicit instance in Remark 9 and say "by computation (§8)". Change the disclaimer to "No proof in Sections 1–7 depends on this section".

8. **minor — §8 "CSEP" (l. 504): the colourings are not always minimum.**
   - **Problem.** The "minimum proper colourings of the square" were produced by `exp_sqcol.min_colouring`. It starts its search at ⌊Δ(K²)/2⌋+1, which is not a lower bound for χ(K²). For 5 of the 85 cubic graphs of order 12, χ(K²) is below that start value (`A18-scripts/sqcol_check.py`), so the colourings used there are not minimum. Larger classes make the hardest test, so this matters for the claim.
   - **Status.** An uncommitted working-tree edit, made during the audit, changes the start to Δ(K)+1, which is valid. The published counts (57/170/150) come from the old code.
   - **Fix.** Rerun with the corrected start and update the counts.

9. **minor — the remark after Lemma `caseI` (l. 391–397).**
   - "𝒜(u)" is undefined for a non-disjoint family.
   - "It is meaningful only if … packed" overstates. The hypothesis can hold without packedness; only its supply by the separation theorem needs it.
   - "Trails of Lovász's induction" is undefined.
   - **Fix.** Use "the union of the sets of 𝒜 containing u", say "can be supplied by Theorem 4 only if", and define or drop "trails".

10. **minor — §8 "MSEP" (l. 481–482): the failure count in the cross-check is wrong.**
    - **Problem.** "285 queries, including 12 failures at distance two" should read **9 failures**. `validate_cubsep.py` counts failures as `sum(r == '0')` over all output tokens. That includes the three zeros in cubsep's summary line, "pairings 0 failures 0 undecided 0", which `given` mode always prints. `A18-scripts/val_dist.py` recounts 9, all at distance 2. E21 repeats the wrong number.
    - **Fix.** Correct the manuscript and E21, and count only the first 285 tokens in the script.

11. **minor — §8 "What does not work", item (b) (l. 521–522): the variant is not stated.**
    - **Problem.** "One forbidden class for every vertex: fails in 114 of 199" is the variant in which the forbidden class may lie at distance 2 (`mind = 2`). At distance ≥ 3 the log gives 79/199, and 0/199 when half the vertices are constrained.
    - Items (a)–(f) are too terse to be checked. For example, (e) does not say which vertex's end path lies in which closed neighbourhood.
    - **Fix.** State each strengthening precisely, with its parameters.

12. **minor/nit — other §8 numbers.**
    - "Instances left undecided … were all certified" (l. 497–498): E21 records only "first batch: 26/26". `search_general.py` was still running during the audit. I certified the 176 undecided instances present at 05:27 (176/176).
    - The random-graph runs give no instance totals.
    - Order 18: `rand_pm` samples with replacement, so the 8,260,200 pairings are not necessarily distinct.
    - "Never failed (540 instances)" (l. 535) includes 1 undecided instance (E21 (G)).
    - **Fix.** Record final totals (instances, undecided, certified) in the manuscript and in E21. Say "sampled with replacement". Say "539 decided".

13. **minor — title, the §6 heading and the abstract item "The Case I lemma".**
    - **Problem.** The Case I statement is Conjecture `EE`, which is open. The proved Lemma `caseI` is a direct check. The title can be read as claiming the lemma is proved.
    - The abstract (l. 64) also says "We also show that every natural strengthening we tried … is false", which is a computational finding.
    - **Fix.** Use "the Case I conjecture" or "the Case I step", and "computations show".

14. **nit — l. 357: the sentence is tautological.** "Lovász's induction proves CSEP as soon as … some neighbour u satisfies (i)": (i) for one u already is the conclusion for K. Say that the induction step at z succeeds with a trivial chain iff (ii) holds for some u, which by Proposition `EE` is (i).

15. **nit — remark after Lemma `rotation` (l. 416–418).** "Letting c_i join the class of c_{i+1}" should say:
    - c_i joins *every* set containing c_{i+1}, so that two vertices c_i, c_j with c_{i+1}, c_{j+1} in one class both join it, which certifies the second hypothesis;
    - {c_i, c_{i+1}} is added when c_{i+1} is classless;
    - all new sets must be packed in K_C.

    This is what `rotate.py` does.

16. **nit — small statements.**
    - Prop. `reduction`(a) uses "no isolated vertices" without saying so.
    - Prop. `cover`: say that L is simple. The quotient in "Reformulations" can be taken simple.
    - Lemma `packedlift` proof: note that ℓ is a leaf, so no new short paths arise.
    - Intro item 2 (l. 101–102): "MSEP is the case of classes of size at most two" needs "and all degrees odd".
    - §6, l. 331: "(whose only positive even vertex is u)": u may be isolated.
    - Results item 3: "at its end vertex" should be "at either end".
    - Abstract l. 58–59: "formalises the reduction to the Gallai class": only part (c) is formalised.

17. **nit — Lean (`MultiSep.lean`).**
    - Docstrings of `sp_case_big` (l. 1013) and `sp_case_leaf` (l. 1199–1200) still say "{c, a}" (copied from `Separation.lean`); they should say X.
    - The module header does not list `SparseFam` / `separation_sparse`.
    - `classSep_caseI` is existential; it does not record that D is "append zu".
    - `realisable_of_*` do not state the path count n/2. It follows from the size identity in `Realisable.lean`; say so in §9.
    - §9 could list `packed_lift` for Lemma `packedlift`.
    - Script nit: in `cubsep.c` `classes` mode, the FAIL line prints zeros (`__builtin_ctz(clsmask[0]) * 0 + 0`) instead of the colouring. Failures would be counted but not recorded.

18. **nit — novelty remark (l. 189–197).** I checked the references:
    - [CW25] (arXiv:2510.12806, Chu–Wang: 3n/5 for Eulerian graphs with triangles pairwise at distance ≥ 3) is accurate.
    - The description of [BS21] is accurate.
    - The novelty claims "we found no source" (reduction class) and "we did not find" (Theorem `endedge`) are suitably hedged.

    Consider also citing Harding–McGuinness, J. Graph Theory 75 (2014). Their bound for girth ≥ 4 is p/2 + ⌊(g+1)q/(2g)⌋, not n/2. This is the nearest result for triangle-free graphs, and it supports the statement that Gallai's conjecture is open on the class.

## Summary

- I found no mathematical error in any proof. Items 1–5 are sound, including the rotation lemma.
- The Lean statements match the manuscript. The file compiles with standard axioms only, and the committed version is sorry-free.
- The substantive problems are in the computational section:
  - the "certified moves" experiment is misdescribed: separate searches, and rotation capped at cycle length 10 at order 12 (finding 1);
  - one wrong count: 12 should be 9 (finding 10);
  - "minimum" square colourings that are not always minimum (finding 8).
- The rest are wording and citation fixes (2–7, 9, 11–18).
