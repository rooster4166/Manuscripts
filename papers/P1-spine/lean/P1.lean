import GallaiLean.Separator
import GallaiLean.EulerianCone
import GallaiLean.TwoEven

/-!
# P1: entry file

Paper: `papers/P1-spine/paper.tex`, *A machine-checked reduction of Gallai's path decomposition
conjecture to two rooted tests on 3-connected graphs*.

Run from `lean/`:  `lake env lean ../papers/P1-spine/lean/P1.lean`.
The expected output is `papers/P1-spine/axioms.expected`.

* Part 1 restates every headline theorem of the paper with its full statement and proves it by
  the library declaration, so a change to a library statement breaks this file.
* Part 2 checks that every other Lean name cited in the paper resolves (`#cited` prints nothing
  and fails on an unknown name).
* Part 3 prints the axioms of every headline theorem. Only `propext`, `Classical.choice` and
  `Quot.sound` may occur.

The imports are the modules the paper uses: `Separator` (the spine, Theorem 1.2, with Lovász's
theorem, Fan's lemma and Theorems 59 and 113 below it), `EulerianCone` (Section 9) and `TwoEven`
(only for `PathDecomp.ends_le_degree`, cited in Lemma 2.2).
-/

open SimpleGraph

/-- `#cited n₁ n₂ …` fails if some name does not resolve to a declaration; otherwise it prints
nothing. -/
elab "#cited " ids:ident* : command => do
  for id in ids do
    try
      discard <| Lean.Elab.Command.liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo id
    catch e =>
      Lean.logErrorAt id e.toMessageData

namespace P1

open Gallai

universe u

/-! ## Part 1: headline theorems, restated -/

/-- **Theorem 1.2** (main theorem; MR Theorem 114): Gallai's conjecture ⇔ the tests on all
3-connected `J` ⇔ the tests on 3-connected `J` with `J − z` free of matching cuts. -/
theorem main_theorem :
    (GallaiConjecture.{u} ↔ SpineTests.{u}) ∧ (GallaiConjecture.{u} ↔ SpineTestsNMC.{u}) :=
  gallai_iff_spineTests'

/-- Theorem 1.2, (i) ⇒ (ii) (Proposition 8.3). -/
theorem gallai_implies_tests (h : GallaiConjecture.{u}) : SpineTests.{u} :=
  spineTests_of_gallai h

/-- Theorem 1.2, (iii) ⇒ (i) (Theorem 8.7), with its three ingredients as hypotheses. -/
theorem tests_implies_gallai (hL : LovaszStatement.{u}) (h59 : Thm59Statement.{u})
    (hsep : SeparatorStatement.{u}) (hT : SpineTestsNMC.{u}) : GallaiConjecture.{u} :=
  gallai_of_spineTestsNMC hL h59 hsep hT

/-- **Lemma 3.4** (Fan's addible-edge lemma, Fan 2005, Lemma 3.4). -/
theorem fan_lemma {U : Type u} [Fintype U] [DecidableEq U] {G G' : SimpleGraph U}
    [DecidableRel G'.Adj] {a b : U} (hab : G.Adj a b)
    (hG' : ∀ e, e ∈ G'.edgeSet ↔ e ∈ G.edgeSet ∧ e ≠ s(a, b)) (D' : PathDecomp G')
    (h : (Finset.univ.filter (fun w => G'.Adj a w ∧ D'.ends w = 0)).card < D'.ends b) :
    ∃ D : PathDecomp G, D.size = D'.size ∧ D.ends a = D'.ends a + 1 ∧
      D.ends b + 1 = D'.ends b ∧ ∀ w, w ≠ a → w ≠ b → D.ends w = D'.ends w :=
  fan_single hab hG' D' h

/-- **Theorem 3.5** (Lovász, strong form): at most one vertex of positive even degree
(`evenSet G`) ⇒ a decomposition with `ends v = deg v mod 2` everywhere. -/
theorem lovasz_strong {W : Type u} [Fintype W] [DecidableEq W] (G : SimpleGraph W)
    [DecidableRel G.Adj]
    (hev : (Finset.univ.filter (fun v => 0 < G.degree v ∧ Even (G.degree v))).card ≤ 1) :
    ∃ D : PathDecomp G, ∀ v, D.ends v = G.degree v % 2 :=
  lovasz_ends G hev

/-- **Theorem 3.6** (Lovász 1968): at most one even vertex ⇒ `p(G) ≤ ⌊N/2⌋`. -/
theorem lovasz_theorem : LovaszStatement.{u} := lovaszStatement

/-- **Theorem 6.2** (MR Theorem 59, finite-order form). -/
theorem theorem59 : Thm59Statement.{u} := thm59

/-- **Theorem 7.2** (separator theorem; MR Theorem 113). -/
theorem theorem113 : SeparatorStatement.{u} := separatorStatement

section cones

variable {W : Type u} [Fintype W] [DecidableEq W] (B : SimpleGraph W) [DecidableRel B.Adj]

omit [DecidableEq W] [DecidableRel B.Adj] in
/-- **Proposition 9.2**: the cone is 3-connected iff the base is 2-connected. -/
theorem cone_threeConnected_iff : KConnected 3 (fullCone B) ↔ KConnected 2 B :=
  kConnected_three_fullCone_iff

omit [Fintype W] [DecidableEq W] [DecidableRel B.Adj] in
/-- **Proposition 9.3**: `J − z` has a matching cut iff `B` has one. -/
theorem cone_matchingCut_iff : HasMatchingCut (delVert (fullCone B) none) ↔ HasMatchingCut B :=
  hasMatchingCut_delVert_fullCone_iff

/-- **Proposition 9.4**: (T1) at the apex is rooted Gallai for the Eulerian base of even order. -/
theorem cone_test1_iff : Test1 (fullCone B) none ↔
    (Even (Fintype.card W) → (∀ a, Even (B.degree a)) → ∀ r, RootedDecomp B r) :=
  test1_fullCone_iff

/-- **Proposition 9.5**, first item: (T2) at the apex is vacuous. -/
theorem cone_test2_apex : Test2 (fullCone B) none := test2_fullCone_apex

/-- **Proposition 9.6**: rooted Gallai is the private-leaf bound. -/
theorem rooted_iff_leaf (r : W) (hev : Even (B.degree r)) (hpos : 0 < B.degree r) :
    RootedDecomp B r ↔ pathNumber (addLeaf B r) ≤ Fintype.card W / 2 :=
  rootedDecomp_iff_addLeaf r hev hpos

/-- **Theorem 9.7(c)**, unrestricted form: at a cone over a base of even order, all tests at all
vertices hold iff rooted Gallai holds at every root of the base whenever it is Eulerian. -/
theorem cone_all_tests_iff (hW : Even (Fintype.card W)) :
    (∀ z, Test1 (fullCone B) z ∧ Test2 (fullCone B) z) ↔
      ((∀ a, Even (B.degree a)) → ∀ r, RootedDecomp B r) :=
  fullConeTests_iff B hW

end cones

/-- **Theorem 9.7(c)**: the spine's weakest form gives RE for every 2-connected Eulerian graph
of even order without a matching cut. -/
theorem spine_gives_RE (h : SpineTestsNMC.{u}) {W : Type u} [Fintype W] [DecidableEq W]
    (B : SimpleGraph W) [DecidableRel B.Adj] (h2 : KConnected 2 B) (hm : ¬ HasMatchingCut B)
    (hW : Even (Fintype.card W)) (hB : ∀ a, Even (B.degree a)) (r : W) : RootedDecomp B r :=
  rootedDecomp_of_spineTestsNMC h B h2 hm hW hB r

/-- **Theorem 9.7(d)**: Gallai's conjecture gives rooted Gallai for every connected Eulerian
graph of even order, at every root of positive degree. -/
theorem gallai_gives_RE (h : GallaiConjecture.{u}) {W : Type u} [Fintype W] [DecidableEq W]
    (B : SimpleGraph W) [DecidableRel B.Adj] (hc : B.Connected) (hW : Even (Fintype.card W))
    (hB : ∀ a, Even (B.degree a)) (r : W) (hpos : 0 < B.degree r) : RootedDecomp B r :=
  rootedDecomp_of_gallai h B hc hW hB r hpos

end P1

/-! ## Part 2: every other Lean name cited in the paper resolves -/

#cited
  Gallai.GPath Gallai.GPath.edges Gallai.GPath.endsAt Gallai.GPath.exists_join
  Gallai.GallaiConjecture Gallai.HasMatchingCut Gallai.HasMatchingCut.of_iso Gallai.InClassC
  Gallai.IsSepComponent Gallai.KConnected Gallai.KConnected.connected
  Gallai.KConnected.delVert_connected Gallai.KConnected.le_degree Gallai.LovaszStatement
  Gallai.MarkedBoundUpTo Gallai.MarkedPartition Gallai.MarkedTwoConnTestUpTo Gallai.PMP
  Gallai.PMP.exists_trim Gallai.PathDecomp Gallai.PathDecomp.ends Gallai.PathDecomp.ends_le_degree
  Gallai.PathDecomp.ends_mod_two Gallai.PathDecomp.exists_internal_of_ends_lt
  Gallai.PathDecomp.exists_split Gallai.PathDecomp.map_injective_ends
  Gallai.PathDecomp.project_full Gallai.PathDecomp.size Gallai.PathDecomp.sum_ends
  Gallai.PathDecomp.trim_ends Gallai.PathDecomp.exists_of_iso Gallai.PathDecomp.mapInj
  Gallai.PathDecomp.append_move Gallai.PathDecomp.reroute_move
  Gallai.R2_on Gallai.R3_on Gallai.RootedAt Gallai.RootedTestsUpTo Gallai.SeparatorStatement
  Gallai.SmallBlocks Gallai.SmallOn Gallai.SmallerMB Gallai.SpineTests Gallai.SpineTestsNMC
  Gallai.TPath Gallai.Test1 Gallai.Test1At Gallai.Test2 Gallai.Thm59Statement
  Gallai.ThreeEndsTestUpTo Gallai.TwoConnOn Gallai.TwoConnected Gallai.TwoConnected.kConnected
  Gallai.addLeaf Gallai.apex Gallai.apex_inClassC Gallai.apex_kConnected_three
  Gallai.apex_outEnds_bound Gallai.attach_pendant Gallai.baseStep Gallai.case1_lift
  Gallai.case2_lift Gallai.cone Gallai.cone_step Gallai.cutStep Gallai.dbl Gallai.delVert
  Gallai.delVert_degree Gallai.doubleLeafStep Gallai.edgesM Gallai.endsL
  Gallai.evenSet
  Gallai.exists_connected_matchingCut Gallai.exists_cut_edge Gallai.exists_decomp_of_edgesM
  Gallai.exists_graft Gallai.exists_graft_x Gallai.exists_leafCost_le
  Gallai.exists_leafCost_le_markedNumber Gallai.exists_localA' Gallai.exists_localX
  Gallai.exists_sepComponent_or Gallai.exists_subst_list Gallai.exists_three_ends
  Gallai.exists_two_ends Gallai.fan_exec Gallai.fan_exists_chain Gallai.fan_single
  Gallai.fanChain_transport Gallai.FanPred Gallai.FanAvoid Gallai.FanChain
  Gallai.floor_on Gallai.fullCone Gallai.fullCone_degree_none Gallai.fullCone_degree_some
  Gallai.fullCone_onlyEven_iff Gallai.fullConeDelIso Gallai.fullConeTests_iff
  Gallai.gallai_iff_markedBound Gallai.gallai_iff_rootedTest
  Gallai.gallai_iff_spineTests Gallai.gallai_iff_spineTests' Gallai.gallai_iff_tests
  Gallai.gallai_of_spineTestsNMC Gallai.glue0 Gallai.glue1 Gallai.glueEnd Gallai.glueJ
  Gallai.glueSplit Gallai.glueU Gallai.hasMatchingCut_delVert_fullCone_iff
  Gallai.kConnected_three_fullCone_iff Gallai.le_outEnds Gallai.leafCost Gallai.leafGraph
  Gallai.leafGraph_trim Gallai.leafStep Gallai.lemma6 Gallai.lovaszStatement Gallai.lovasz_ends
  Gallai.lovasz_on Gallai.lovasz_tight Gallai.markedBoundUpTo_of_tests
  Gallai.markedBound_of_classC Gallai.markedNumber Gallai.markedNumber_add_card_le
  Gallai.markedNumber_anti Gallai.markedNumber_le_insert Gallai.markedNumber_singleton_add_one
  Gallai.matchingCut_markedBound Gallai.mbOn_of_testsUpTo Gallai.minOutEnds_eq
  Gallai.not_hasMatchingCut_delVert_apex Gallai.not_unique_odd Gallai.pathNumber
  Gallai.pathNumber_addLeaf_le Gallai.pathNumber_le_markedNumber_add Gallai.pendantStep
  Gallai.residue_sep Gallai.restrict Gallai.RootedDecomp Gallai.RootedTest
  Gallai.rootedAt_evenComp_evenPorts Gallai.rootedAt_evenComp_oddPorts Gallai.rootedAt_oddComp
  Gallai.rootedAt_of_few_even Gallai.rootedAt_of_lift Gallai.rootedAt_of_tests
  Gallai.rootedDecomp_iff_addLeaf Gallai.rootedDecomp_of_gallai
  Gallai.rootedDecomp_of_spineTestsNMC Gallai.rootedTest_of_gallai Gallai.separatorStatement
  Gallai.separator_theorem Gallai.sideA Gallai.sideA_parity Gallai.sideA_port_pos Gallai.sideE
  Gallai.sideE_induce_connected Gallai.sideE_port_pos Gallai.singleton_step
  Gallai.spineTests_of_gallai Gallai.test1At_fullCone_iff Gallai.test1_fullCone_iff
  Gallai.test1_fullCone_some Gallai.test1_of_gallai Gallai.test2_fullCone_apex
  Gallai.test2_fullCone_some_of_even Gallai.test2_of_gallai Gallai.thm59
  Gallai.threeEnds_of_classC Gallai.twoConnStep Gallai.two_le_card_of_odd
  Gallai.two_mul_pathNumber_addLeaf_le

/-! ## Part 3: axioms of the headline theorems -/

#print axioms P1.main_theorem
#print axioms P1.gallai_implies_tests
#print axioms P1.tests_implies_gallai
#print axioms P1.fan_lemma
#print axioms P1.lovasz_strong
#print axioms P1.lovasz_theorem
#print axioms P1.theorem59
#print axioms P1.theorem113
#print axioms P1.cone_threeConnected_iff
#print axioms P1.cone_matchingCut_iff
#print axioms P1.cone_test1_iff
#print axioms P1.cone_test2_apex
#print axioms P1.rooted_iff_leaf
#print axioms P1.cone_all_tests_iff
#print axioms P1.spine_gives_RE
#print axioms P1.gallai_gives_RE
