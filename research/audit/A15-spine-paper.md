# Audit A15: the spine paper (`manuscripts/spine/spine.tex`)

**Target.** `manuscripts/spine/spine.tex` is a standalone paper, 27 pages, that compiles with pdflatex. It proves that Gallai's conjecture is equivalent to the two deletion tests on 3-connected graphs (marked-reduction (MR) Theorem 114). The proof runs through:

- MR Theorem 1 (finite-order block transfer);
- MR Theorem 7, matching-cut case, with MR Lemma 6;
- MR Theorem 59;
- MR Theorem 113.

It follows the Lean proof `Gallai.gallai_iff_spineTests'`.

**Question.** Is every proof in the paper complete and correct? Do its statements, definitions and Lean citations match the Lean library? Does it use the corrected forms recorded in audits A1, A2 and A14?

## 0. Verdict

**No mathematical error was found.** Two independent adversarial referees each re-derived every inequality, floor computation, parity claim, case split and path-surgery step in their half of the paper:

- Sections 1–4: preliminaries, marked numbers, block transfer, matching cuts;
- Sections 5–8: Theorem 59, the separator theorem, Theorem 114, the formalisation section.

The referees reported:

- **One expository ERROR (A.1).** A false sentence about how Lovász's theorem is used. No mathematics was affected.
- **One GAP against the paper's own claim (A.2 = B.1).** The paper first claimed to be "self-contained", but it quotes Lovász's and Hall's theorems without proof.
- **Several MISMATCHes.** Lean pointers, attributions to MR and A14, and the formalisation status of three auxiliary statements.
- **MINOR items.** Exposition and notation.

All findings are fixed in the committed version (§3).

**Lean side, rechecked after the fixes.**

- `lake build` succeeds. The last full build, after merging `claude/quirky-dirac-d9km1q`, ran 18372 jobs.
- `manuscripts/spine/SpineAxioms.lean` prints only `propext`, `Classical.choice` and `Quot.sound` for all 14 main declarations.
- `manuscripts/spine/SpineCheck.lean` runs `#check` on all 141 Lean names that the paper cites, and all of them resolve.
- Both referees checked every file:line entry in the correspondence table by grep. The only wrong entry was the name flagged in B.2, now fixed.

## 1. Method

1. **Writing.** The paper was written from the Lean sources: `ThreeConnected`, `Separator*`, `SmallBounds`, `PathSurgery`, `Thm59*`, `MarkedBlocks`, `MarkedSurgery`, `Marked`, `PrivateLeaf`, `Doubling` and `Lovasz`. It was also checked against MR and audits A1, A2, A8 and A14. Where Lean is simpler than MR, the paper follows Lean.
2. **Self-checks by the author.** The scripts are in `research/audit/A15-scripts/`.
   - `arith.py` brute-forces every budget inequality in the paper over small parameters (0 failures). It covers:
     - all cut-vertex cases 1a, 1b, 2a, 2b and 2c;
     - leaf cases L1–L5, the double leaf and the pendant case;
     - the floor chain of Theorem 4.11 and the Lemma 6 count;
     - the cone step, singletons and general S;
     - Lemma 6.4 and the root-analysis lifts;
     - the test budgets and the final Gallai bound;
     - the bridge double.
   - `parity.py` checks two parity claims on random graphs (0 failures):
     - the even vertices of J = B + z(S) in Proposition 7.6, 9982 instances;
     - the port parity of Lemma 6.3(c), 6162 instances.
3. **Two fresh adversarial referees.** These were subagents with no access to the author's reasoning. Each was given the paper and the Lean sources and asked to find errors, gaps and mismatches. One covered Sections 1–4 and the other Sections 5–8. Both ran the Lean check files. Their findings are listed below as A.n and B.n.

## 2. What the referees confirmed

**Sections 1–4.**

- Definition 1.1 and Theorem 1.1 match `Test1`, `Test2`, `SpineTests`, `SpineTestsNMC`, `GallaiConjecture` and `gallai_iff_spineTests'` exactly. This covers hypotheses, the natural-number budgets (exact because of the forced parities), `D.ends` as b_D, and the quantifier order.
- Lemmas 2.1–2.5 and Corollary 2.7 are correct. Theorem 2.6 is exactly `LovaszStatement`.
- The cone inequality and the Hall assignment lemma are correct and match `le_outEnds`/`apex_outEnds_bound` and `markedNumber_add_card_le`. The Hall lemma's integrality step was checked.
- The gluing lemma (G1)–(G6) matches `glue0`, `glue1`, `glueJ`, `glueU`, `glueEnd` and `glueSplit`. The trim and attach lemma matches `PMP.exists_trim` and `attach_pendant`.
- Steps 0–5 of the block transfer are exhaustive and in the order of `mbOn_of_testsUpTo`.
- Every case of the cut, leaf, double-leaf, pendant and residue lemmas was re-derived.
- Lemma 4.8 (connected shores), Lemma 4.9 (leaf trimming) and Lemma 4.10 (Lemma 6) are correct, and so is the floor chain of Theorem 4.11.

**Sections 5–8.**

- Theorem 5.2's induction on the block bound is well-founded. The matching-cut branch uses (MB_{n−1}) with n − 1 < j. (B_j) is vacuous on graphs with a matching cut.
- The cone step, singletons (all parities) and general S are correct.
- Lemmas 6.3–6.5 are correct.
- In all four separator cases, the exterior graph has order n − 2s and the root degree has the correct parity and is positive.
- Every vertex-intersection claim in Propositions 6.7 and 6.8 holds.
- The even/even lift (Lemma 6.10), phases x and y with properties P1–P5, was re-derived line by line. This includes the degenerate situations: q₁ or q₃ trivial, X ending at y, Y = N₁, w₀ on R₀, and t = y.
- Lemmas 7.1–7.5 are correct.
- In Proposition 7.6, |S| is even in both cases and the even vertices of J are exactly {z} or {z, r}.
- Theorem 7.7's induction uses m = n − 2 and (RT_{n−1}).
- The statements of RootedAt, Thm59Statement, MarkedBoundUpTo, IsSepComponent and SeparatorStatement match the paper.
- The quoted `gallai_iff_spineTests'` is verbatim. The toolchain and the Mathlib tag are both v4.36.0.
- The library contains no `sorry`, no `axiom` and no `native_decide`.

## 3. Findings and fixes

Severity: ERROR = false statement or invalid step; GAP = missing argument; MISMATCH = disagreement with Lean or a source; MINOR = exposition.

### Referee A: Sections 1–4

| # | Severity | Finding | Fix |
|---|---|---|---|
| A.1 | ERROR (expository) | §2.3 said Lovász's theorem is used "only in the following form" (Cor. 2.7). In fact Theorem 2.6 is used directly in Prop. 5.4, Lemma 6.9(a) and Lemma 7.5. | The sentence now says the statement itself is used, together with the tight form. |
| A.2 | GAP | The abstract and intro claimed a "self-contained" proof, but Lovász's and Hall's theorems are quoted without proof. | The abstract now says the two classical theorems are quoted without proof and every other proof is given in full. Both theorems are proved in the library or Mathlib (§8). |
| A.3 | MISMATCH | The intro called three items "simplifications" of MR that are not: the pendant parity, connected shores, and block-order induction. It also attributed every departure to A14, which records only some of them. | The list is rewritten. Each item now names its source: A14, the `MarkedBlocks.lean` documentation, the proofs in `ThreeConnected.lean`, or `lean/README.md` "Deviations". Connected shores and block-order induction are described as organisational. The pendant item now says the step matches MR, and the remark after Lemma 4.6 is corrected the same way. |
| A.4 | MISMATCH | Lemma 2.3(c) cited `PMP.exists_join`, a statement about partial marked partitions. | Now cites `GPath.exists_join` (MarkedSurgery:409), in the lemma and in the table. |
| A.5 | MISMATCH | b_D(v) ≤ d(v) and "k-connected ⇒ connected" had no Lean citation. | Added `PathDecomp.ends_le_degree` (TwoEven:1084) and `KConnected.connected` (ThreeConnected:98). |
| A.6 | MISMATCH (minor) | The Lean tests (A_m), (B_m) quantify over `TwoConnected` (no cut vertex), not `KConnected 2`. | §2.1 now states this and names the conversion `TwoConnected.kConnected`. |
| A.7 | MINOR | The text said "four lemmas"; there are five. | Corrected. The text now notes that Lemma 4.7 is about any connected graph. |
| A.8 | MINOR | The paper gave the wrong reason why each mark absorbs at most one path. | The reason is now injectivity of σ and σ being a map. |
| A.9 | MINOR | "Odd vertices have an end … as soon as they have positive degree" contains a redundant qualifier. | Removed. |
| A.10 | MINOR | p(K_{2k+1}) ≥ k+1 needs k ≥ 1. | Added. |
| A.11 | MINOR | Theorem 4.11 reused z, x and a with other meanings. | Renamed to ζ, v and α (and μ, ν in the last step). |
| A.12 | MINOR | "Theorem 113 under the two hypotheses its proof uses (A2, F7)": F7's second hypothesis is the rooted tests, not (MB_{n−2}). | Reworded. Theorem 6.2 is now called a strengthening of F7, and the text says F7's hypothesis implies (MB_{n−2}) via Theorem 59. |
| A.13 | MINOR | In (T2), r was not quantified. | Now "for every neighbour r of z", matching `Test2`. |
| A.14 | MINOR | Some steps were terse: connectivity of G − w, G − w − w′ and G_2; 2k+1 ≤ m in Lemma 4.6; one sentence ungrammatical. | Each terse step now has its one-line justification, and the sentence is fixed. |

### Referee B: Sections 5–8

| # | Severity | Finding | Fix |
|---|---|---|---|
| B.1 | GAP | Same as A.2. | As A.2. |
| B.2 | MISMATCH | The table named `exists_internal_of_ends_lt` without its namespace, and omitted the join lemma. | Now `PathDecomp.exists_internal_of_ends_lt` and `GPath.exists_join`. |
| B.3 | MISMATCH | Lemma 6.10 is stated for all v ∉ C at decomposition level. `case1_lift`/`case2_lift` give only the replacement family M, with ends at one root r; the assembly happens in `rootedAt_evenComp_evenPorts`. | The citation and the table now say exactly this. |
| B.4 | MINOR | §8 said every result of §§2–7 is in Lean. Remark 5.5 is not formalised, and Lemma 7.2 is formalised only for H = J − z. | §8.1 now lists the three statements that are formalised only in the form the main proof needs, or not at all. |
| B.5 | MINOR | `SpineCheck.lean` missed 8 names cited in §8. | Regenerated from the paper: 141 names, all resolve. |
| B.6 | MINOR | The quoted definitions omitted `GPath.edges`, `GPath.endsAt` and `PathDecomp.size`, and namespaced names were shown expanded without saying so. | Added the three definitions, plus a note that namespaces are expanded and the comments are ours. |
| B.7 | MINOR | Several cited declarations take `LovaszStatement`, `Thm59Statement` or `SeparatorStatement` as hypotheses. | §8.1 now says so and names the theorems that discharge them. |
| B.8 | MINOR | The separator theorem heading said "in the form of A2, F7". | Now "a strengthening of A2, F7". |
| B.9 | MINOR | The proof of Lemma 6.6 (surgery) was terse: "pieces meet only at a, b", "(c) Similar". | Now spells out the vertex-intersection and end identities, including the trivial-piece cases. |
| B.10 | MINOR | "In the last case \|S\| ≥ 4": \|S\| is even in both cases. | Now "in both cases". |
| B.11 | MINOR | "b(x)" was undecorated in Prop. 5.4(b). Lemma 6.3(b) reused w from the proof of (a). | Fixed both. |
| B.12 | MINOR | §8.4 said the representation choices "differ" from the paper, then said one is "exactly as in Section 6". | Reworded. |
| B.13 | MINOR | `R2_on`/`R3_on` are parts (a)/(b) of Lemma 6.4 (the digits count ends), not (R1)/(R2). | The citation and table now say which part each proves. |
| B.14 | MINOR | The table had no rows for `sideA`/`sideE`, `TPath`/`exists_decomp_of_edgesM`, `delVert_degree`, `addLeaf`, `apex`, `cone`, `leafCost`. | Rows added. |
| B.15 | MINOR | The induction measure of Lovász's theorem was misdescribed as the degree sum. | Corrected to Σ d(v) + [no vertex of positive even degree]. |

## 4. Corrections to MR used by the paper

These are the corrected forms from earlier audits.

| Source | Item | How the paper handles it |
|---|---|---|
| A1, G1 | Theorem 1 restricted to even marks | Theorem 3.6 is stated for every nonempty marking. |
| A1, G3 | q(F, ∅) | Defined as p(F) (Def. 3.1). |
| A1, G4 | The bridge formula | Not used; see `MarkedBlocks.lean`. |
| A1, G6 | "Three or more parts" | Only the matching-cut case of Theorem 7 is used. |
| A1, G7 | Even-mark tests | The marked tests on C are proved for every marking (Prop. 5.4). |
| A1, G10 | Instances of order m+1 | Named after Theorem 5.2. |
| A1, G2, G8, G9 | — | Concern W(F,S), Theorem 57 and the doubles, none of which is used. |
| A2, F1 | Theorem 59 conclusion | Theorem 5.2 has the explicit marked-bound conclusion. |
| A2, F6 | Single deletions | Covered in the apex lemma (Lemma 7.4). |
| A2, F7 | Theorem 113 hypotheses | Theorem 6.2 assumes only that B is 2-connected and (MB_{n−2}); it assumes neither minimality nor the absence of a matching cut. |

## 5. Residual items

- **Two classical theorems are quoted, not proved:** Lovász (1968) and Hall (1935). Both are machine-checked:
  - Lovász's theorem in `GallaiLean/Lovasz.lean`, from Fan's lemma proved in `Fan.lean`;
  - Hall's theorem in Mathlib (`Finset.all_card_le_biUnion_card_iff_exists_injective`).
- **Remark 5.5 is not formalised.** It says Gallai implies the rooted tests, so that MR Theorem 59 is an equivalence. It is not part of the main theorem.
- **Bibliography.** The referee checked the bibliographic data of the literature cited in the introduction. The bridge from published results to this paper is limited to Lovász's theorem.
