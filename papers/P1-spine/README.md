# P1. A machine-checked reduction of Gallai's path decomposition conjecture to two rooted tests on 3-connected graphs

**Status: complete.** Every numbered result is proved in the text and, with the exceptions marked
below, formalised in Lean. The headline theorem (Theorem 1.2) is a single Lean theorem with no
hypotheses, depending only on `propext`, `Classical.choice` and `Quot.sound`. There are no
computer-assisted claims and no conjectures among the numbered results. The only result quoted
without proof is Hall's marriage theorem (used in Lemma 4.4).

## Contents

| File | What it is |
|---|---|
| `paper.tex`, `paper.pdf` | The paper (34 pages; `pdflatex` three times, no bibtex: `thebibliography`) |
| `lean/P1.lean` | Lean entry file: restates the headline results, checks every cited name, prints axioms |
| `axioms.expected` | Exact expected output of `lake env lean ../papers/P1-spine/lean/P1.lean` (run from `lean/`) |
| `reproduce.sh` | End-to-end reproduction (`--quick`: entry file + name map + PDF; default adds `lake build`) |
| `scripts/check_names.py` | Every Lean name cited in `paper.tex` is checked by `P1.lean` |
| `scripts/locate.sh` | Current `file:line` of every cited declaration |
| `data/toolchain.txt` | Toolchain versions used for `axioms.expected` and `paper.pdf` |
| `SHA256SUMS` | Checksums of the files above |

Sources superseded by this paper: `manuscripts/spine` (audit A15), `manuscripts/lovasz-fan`, and
Section 2 of `manuscripts/eulerian-cone` (audit A30). The mathematics of the spine is that of the
marked-reduction manuscript MR (`gallai/01-original-manuscripts/marked-reduction.pdf`, unrefereed);
the paper does not depend on MR for correctness, since every proof is given in full.

## Reproduce

```bash
export PATH=$HOME/.elan/bin:$PATH
(cd ../../lean && lake exe cache get)     # Mathlib cache, once
./reproduce.sh --quick                    # seconds, given a built library
./reproduce.sh                            # adds a full `lake build` (about 5 min on 4 cores)
../../scripts/check_papers.sh P1          # the repository-level check for this paper
```

## Claim map

All Lean names are in namespace `Gallai`, files in `lean/GallaiLean/`. Restated in `P1.lean` means
the full statement is repeated there and proved by the library declaration.

| Result | Statement | Proof in paper | Lean | Restated in `P1.lean` |
|---|---|---|---|---|
| Def. 1.1 | Tests (T1), (T2) | — | `Test1`, `Test2` (ThreeConnected) | (via Thm 1.2) |
| **Thm 1.2** | Gallai ⇔ (T1)∧(T2) on 3-connected J ⇔ same with J − z free of matching cuts (MR Thm 114) | §8, end | `gallai_iff_spineTests'` (Separator) | `P1.main_theorem`, `P1.gallai_implies_tests`, `P1.tests_implies_gallai` |
| **Thm 1.3** | Lovász, strong form | §3 (= Thm 3.5, 3.6) | `lovasz_ends`, `lovaszStatement` (Lovasz) | `P1.lovasz_strong`, `P1.lovasz_theorem` |
| Def. 1.4 | RE(B, r) | — | `RootedDecomp` (EulerianCone) | — |
| **Thm 1.5** | Cones (= Thm 9.7) | §9 | see Thm 9.7 | see Thm 9.7 |
| Lem. 2.1 | k-connected ⇒ min degree, connectivity | §2 | `KConnected.le_degree`, `.connected`, `.delVert_connected` | — |
| Lem. 2.2 | Parity of ends | §2 | `PathDecomp.sum_ends`, `.ends_mod_two`, `.ends_le_degree` | — |
| Lem. 2.3 | Splitting and joining | §2 | `PathDecomp.exists_split`, `.exists_internal_of_ends_lt`, `GPath.exists_join` | — |
| Lem. 2.4 | Two and three ends | §2 | `exists_two_ends`, `exists_three_ends` | — |
| Lem. 2.5 | Private leaves | §2 | `PathDecomp.trim_ends`, `pathNumber_addLeaf_le`, `exists_leafCost_le` | — |
| Def. 3.1 | Predecessors, chains | — | `FanPred`, `FanAvoid`, `FanChain` (Fan) | — |
| Lem. 3.2 | Executing a chain | §3.1 | `fan_exec`, `PathDecomp.append_move`, `PathDecomp.reroute_move`, `fanChain_transport` (Fan, FanMoves) | — |
| Lem. 3.3 | Existence of a chain (counting) | §3.1 | `fan_exists_chain` (Fan; for a set of donors) | — |
| **Lem. 3.4** | Fan's addible-edge lemma (Fan 2005, Lemma 3.4) | §3.1 | `fan_single` (Fan) | `P1.fan_lemma` |
| **Thm 3.5** | Lovász, strong form | §3.2 | `lovasz_ends` | `P1.lovasz_strong` |
| **Thm 3.6** | Lovász (1968) | §3.2 | `lovaszStatement` | `P1.lovasz_theorem` |
| Cor. 3.7 | Tight form | §3.2 | `lovasz_tight`, `lovasz_on` (SmallBounds) | — |
| Def. 4.1, Lem. 4.2 | Marked number and its basic properties | §4 | `MarkedPartition`, `markedNumber`, `pathNumber_le_markedNumber_add`, `markedNumber_anti`, `markedNumber_le_insert`, `markedNumber_singleton_add_one`, `exists_leafCost_le_markedNumber` | — |
| Lem. 4.3 | Cone inequality | §4 | `le_outEnds`, `apex_outEnds_bound` | — |
| Lem. 4.4 | Assignment lemma (Hall) | §4 | `markedNumber_add_card_le` (Thm59Hall) | — |
| Def. 4.5, Thm 4.6 | Block transfer (MR Thm 1, finite form) | §5 | `mbOn_of_testsUpTo`, `markedBoundUpTo_of_tests` | — |
| Lem. 5.1–5.7 | Gluing, pendant edges, cut vertices, leaves, double leaf, pendant configuration, residue | §5 | `glue*`, `PMP.exists_trim`, `attach_pendant`, `cutStep`, `leafStep`, `doubleLeafStep`, `pendantStep`, `residue_sep` (MarkedBlocks, MarkedSurgery) | — |
| Lem. 5.8–5.10, Thm 5.11 | Matching cuts (MR Lemma 6, Thm 7) | §5 | `exists_connected_matchingCut`, `leafGraph_trim`, `lemma6`, `matchingCut_markedBound` | — |
| Def. 6.1 | Rooted tests RT | — | `RootedAt`, `RootedTestsUpTo` | — |
| **Thm 6.2** | MR Theorem 59, finite-order form | §6 | `thm59 : Thm59Statement` (Thm59) | `P1.theorem59` |
| Lem. 6.3, Prop. 6.4 | Cones stay in C; marked tests on C | §6 | `apex_inClassC`, `cone_step`, `singleton_step`, `markedBound_of_classC`, `threeEnds_of_classC` | — |
| Rem. 6.5 | Converse of Thm 59 | §6 (sketch via Lem. 8.2) | not formalised | — |
| Def. 7.1 | Separated component | — | `IsSepComponent` | — |
| **Thm 7.2** | Separator theorem (MR Theorem 113) | §7 | `separatorStatement : SeparatorStatement` (Separator) | `P1.theorem113` |
| Lem. 7.3–7.10, Prop. 7.7, 7.8, 7.11 | Sides, smaller bounds, root analysis, surgery, the three cases | §7 | `sideA_*`, `sideE_*`, `R2_on`, `R3_on`, `floor_on`, `rootedAt_of_lift`, `exists_subst_list`, `exists_graft`, `rootedAt_oddComp`, `rootedAt_evenComp_oddPorts`, `exists_localX`, `case1_lift`, `case2_lift`, `rootedAt_evenComp_evenPorts` | — |
| Lem. 7.10 | The lift | §7 | formalised with the ends preserved at the chosen root | — |
| Lem. 8.1 | Bridge double | §8 | `dbl`, `two_mul_pathNumber_addLeaf_le`, `rootedTest_of_gallai` (Doubling) | — |
| Lem. 8.2 | Rooted bounds from Gallai | §8 | (a) in general: `rootedTest_of_gallai` + `rootedDecomp_iff_addLeaf`; (b) only for H = J − z, inside `test2_of_gallai` | — |
| Prop. 8.3 | Gallai ⇒ tests | §8 | `spineTests_of_gallai` | `P1.gallai_implies_tests` |
| Lem. 8.4–8.5, Prop. 8.6 | Apex lemma, few even vertices, tests ⇒ rooted tests | §8 | `apex_kConnected_three`, `rootedAt_of_few_even`, `rootedAt_of_tests` | — |
| Thm 8.7 | Tests ⇒ Gallai | §8 | `gallai_of_spineTestsNMC` | `P1.tests_implies_gallai` |
| Prop. 9.1 | Degrees in a cone | §9 | `fullCone_degree_none`, `fullCone_degree_some`, `fullCone_onlyEven_iff` (EulerianCone) | — |
| **Prop. 9.2** | Cone 3-connected ⇔ base 2-connected | §9 | `kConnected_three_fullCone_iff` | `P1.cone_threeConnected_iff` |
| **Prop. 9.3** | Matching cuts of J − z and B | §9 | `hasMatchingCut_delVert_fullCone_iff` | `P1.cone_matchingCut_iff` |
| **Prop. 9.4** | (T1) at the apex ⇔ rooted decompositions of the base | §9 | `test1At_fullCone_iff`, `test1_fullCone_iff` | `P1.cone_test1_iff` |
| Prop. 9.5 | The other tests at a cone are vacuous | §9 | `test2_fullCone_apex`, `test1_fullCone_some`, `test2_fullCone_some_of_even` | `P1.cone_test2_apex` (first item) |
| **Prop. 9.6** | RD(B, r) ⇔ p(B^r) ≤ n/2 | §9 | `rootedDecomp_iff_addLeaf` | `P1.rooted_iff_leaf` |
| **Thm 9.7** | Cones: (a)–(d); (iii) ⇒ RE on 2-connected Eulerian graphs of even order without matching cut; Gallai ⇒ RE | §9 | `rootedDecomp_of_spineTestsNMC`, `fullConeTests_iff`, `rootedDecomp_of_gallai` | `P1.spine_gives_RE`, `P1.cone_all_tests_iff`, `P1.gallai_gives_RE` |
| Ex. 9.8 | K_{2,6} has no matching cut | §9 | not formalised | — |
| Cor. 10.1 | Shape of a smallest counterexample | §10 | not a separate declaration (steps of `rootedAt_of_tests`, `gallai_of_spineTestsNMC`) | — |

## Dependencies

- On other papers: none. P2, P3 and P4 are cited by title in §10 only as the continuation of the
  programme; nothing in P1 depends on them.
- On the manuscript collection: none for correctness. MR is credited as the source of the spine,
  and every departure from it is listed in §1.
- On external results: Hall's theorem (Hall 1935), quoted; Fan's Lemma 3.4 is proved in §3.
