/-
  P3. Reversible lifts from constrained Lovász decompositions to the spine tests.

  Lean entry file of the paper. It imports the library modules the paper uses, proves three short
  new corollaries (Section "New in P3" below: the full parity of the (T2) base graph, and the
  bridges L_N ⇒ (T2) and CL ⇒ (T2)), checks every headline theorem and prints its axioms.

  Run from the `lean/` directory of the repository:
      lake env lean ../papers/P3-reversible-lifts/lean/P3.lean
  The lines `... depends on axioms: [...]` must agree with `../axioms.expected`.
-/
import GallaiLean.ThreeConnected
import GallaiLean.Fan
import GallaiLean.DirectTest1
import GallaiLean.ForestLift
import GallaiLean.Test1AllOdd
import GallaiLean.Test2Lift
import GallaiLean.Test2Converse
import GallaiLean.TriangleBase
import GallaiLean.DLOne
import GallaiLean.ConstrainedLovasz
import GallaiLean.NoData
import GallaiLean.MultiToken
import GallaiLean.MultiTokenObstruct
import GallaiLean.StarTerminal
import GallaiLean.T6Dense
import GallaiLean.TerminalMatching
import GallaiLean.TightFan
import GallaiLean.Separator

open SimpleGraph

namespace Gallai

universe u

/-! ## New in P3 -/

section P3new

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- **The (T2) base graph is all-odd** (paper, Lemma "parities of the (T2) base"): for forest data
`ForestData2 J z r T L`, every vertex of `M = J − zT − Φ` has odd degree, `z` included.
(`Test2Lift.lean` proves this at `r` and at the children, which is all the lift needs.) -/
theorem ForestData2.forM2_odd_all {J : SimpleGraph V} [DecidableRel J.Adj] {z r : V}
    {T : List V} {L : List (V × V)} (hF : ForestData2 J z r T L)
    (hzr : ∀ v, Even (J.degree v) ↔ v = z ∨ v = r) (v : V) :
    (forM2 J z T L).degree v % 2 = 1 := by
  obtain ⟨hzr', hzT, hrT, hTnd⟩ := hF.facts
  have h := hF.forM2_degree v
  have ht := hF.tjoin v
  by_cases hvz : v = z
  · rw [hvz] at h ⊢
    have h0 : (L.map pairEdge).countP (fun e => decide (z ∈ e)) = 0 := by
      rw [List.countP_eq_zero]
      intro e he
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
      obtain ⟨h1, h2⟩ := hF.avoid_z p hp
      simp [pairEdge, Ne.symm h1, Ne.symm h2]
    have hdz : J.degree z = T.length + 1 := by
      rw [← card_neighborFinset_eq_degree]
      have hN : J.neighborFinset z = (r :: T).toFinset := by
        ext x
        rw [mem_neighborFinset, List.mem_toFinset, hF.nbr x, List.mem_cons]
      rw [hN, List.toFinset_card_of_nodup hF.nodup, List.length_cons]
    simp only [ite_true, hzT, ite_false, h0] at h
    omega
  · by_cases hvr : v = r
    · rw [hvr]; exact hF.forM2_odd_r hzr
    · have hodd : J.degree v % 2 = 1 :=
        Nat.odd_iff.mp (Nat.not_even_iff_odd.mp (fun he => by
          rcases (hzr v).1 he with h' | h'
          · exact hvz h'
          · exact hvr h'))
      simp only [hvz, hvr, ite_false, false_or, zero_add] at h ht
      split_ifs at h ht <;> omega

/-- The (T2) base graph has no vertex of positive even degree. -/
theorem ForestData2.evenSet_forM2 {J : SimpleGraph V} [DecidableRel J.Adj] {z r : V}
    {T : List V} {L : List (V × V)} (hF : ForestData2 J z r T L)
    (hzr : ∀ v, Even (J.degree v) ↔ v = z ∨ v = r) : (evenSet (forM2 J z T L)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro v hv
  simp only [evenSet, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  have := hF.forM2_odd_all hzr v
  rw [Nat.even_iff] at hv
  omega

/-- **`L_N` gives (T2) at every root with matching data** (paper, Theorem "bridges", (T2) part).
`L` is a perfect matching of `J[N(z)]` by edges of `J`, written as (child, parent) pairs, that is
(T2) forest data (`ForestData2`); the parity condition at `r` forces `r` to be the parent of its
pair. -/
theorem test2At_of_LN_matching (hLN : LN.{u}) (J : SimpleGraph V) [DecidableRel J.Adj] {z r : V}
    (hzr : ∀ v, Even (J.degree v) ↔ v = z ∨ v = r) (hr3 : 3 ≤ J.degree r)
    {T : List V} {L : List (V × V)} (hF : ForestData2 J z r T L)
    (hnd : (L.map Prod.fst ++ L.map Prod.snd).Nodup) : Test2At J z r := by
  have hodd := hF.forM2_odd_all hzr
  obtain ⟨D₀, hD₀, hi⟩ := hLN V (forM2 J z T L) (hF.evenSet_forM2 hzr) L hnd
    (fun p hp => ⟨hodd p.1, fun h => h.2 (List.mem_append_right _ (List.mem_map_of_mem hp))⟩)
  refine test2At_of_forestBase2 J hzr hr3 ⟨T, L, hF, D₀, hD₀, hi, ?_⟩
  intro p hp q hq hne heq
  exfalso
  have hsnd : (L.map Prod.snd).Nodup := (List.nodup_append.mp hnd).2.1
  exact hne (congrArg Prod.fst (List.inj_on_of_nodup_map hsnd hp hq heq))

/-- **CL gives (T2) at every root with cherry data** (paper, Theorem "bridges"): (T2) forest data
whose forest has distinct parents and no chain of three pairs. -/
theorem test2At_of_cherryLN (hC : CherryLN.{u}) (J : SimpleGraph V) [DecidableRel J.Adj]
    {z r : V} (hzr : ∀ v, Even (J.degree v) ↔ v = z ∨ v = r) (hr3 : 3 ≤ J.degree r)
    {T : List V} {L : List (V × V)} (hF : ForestData2 J z r T L)
    (hpar : (L.map Prod.snd).Nodup)
    (hdepth : ∀ p ∈ L, ∀ q ∈ L, p.2 = q.1 → ∀ s ∈ L, q.2 ≠ s.1) : Test2At J z r := by
  have hCL : CherryList (forM2 J z T L) L :=
    { children := hF.children
      parents := hpar
      nonadj := fun p hp h => h.2 (List.mem_append_right _ (List.mem_map_of_mem hp))
      irrefl := fun p hp => (hF.edge p hp).ne
      depth := hdepth }
  obtain ⟨D₀, hD₀, hi, hii⟩ := hC V (forM2 J z T L) L (hF.evenSet_forM2 hzr) hCL
  exact test2At_of_forestBase2 J hzr hr3 ⟨T, L, hF, D₀, hD₀, hi, hii⟩

end P3new

end Gallai

/-! ## The tests and the open statements (definitions; no axioms to check) -/

#check @Gallai.Test1At
#check @Gallai.Test2At
#check @Gallai.LN
#check @Gallai.DisjL1
#check @Gallai.CherryLN
#check @Gallai.TriangleBaseConj

/-! ## Headline theorems, with their axioms -/

-- §1: the spine, for context (paper P1)
#print axioms Gallai.gallai_iff_spineTests'
-- §2: tools
#print axioms Gallai.exists_two_ends
#print axioms Gallai.exists_three_ends
#print axioms Gallai.append_forest
#print axioms Gallai.append_forest_ends
#print axioms Gallai.PathDecomp.drop_terminal
#print axioms Gallai.test1At_of_leafDecomp
#print axioms Gallai.test2At_of_leafDecomp
-- §3: lifts for (T1)
#print axioms Gallai.test1At_of_triangleBase
#print axioms Gallai.test1_of_triangleBaseConj
#print axioms Gallai.test1At_of_forestBase
#print axioms Gallai.test1_of_forestBases
#print axioms Gallai.twoEnds_of_oddBase
#print axioms Gallai.test1At_of_oddBase
#print axioms Gallai.oddBase_of_matching
#print axioms Gallai.test1At_of_matchingOdd
-- §4: lifts for (T2)
#print axioms Gallai.test2At_of_forestBase2
#print axioms Gallai.test2_of_forestBases2
#print axioms Gallai.forestBase2_matching_of_terminal
#print axioms Gallai.forestBase2_matching_of_test2
#print axioms Gallai.test2At_of_floor
#print axioms Gallai.floor_of_floorBase
#print axioms Gallai.floor_of_matchingBase
#print axioms Gallai.test2At_of_floorBase
#print axioms Gallai.matchingFloorBase_of_terminal
#print axioms Gallai.test2At_of_pairAvoid
#print axioms Gallai.test2At_of_pair_farApart
#print axioms Gallai.test2At_of_pair_steer2
-- §5: bridges
#print axioms Gallai.triangleBase_of_packed
#print axioms Gallai.triangleBase_of_farApart
#print axioms Gallai.triangleBase_of_disjL1
#print axioms Gallai.triangleBase_of_disjL1_reach
#print axioms Gallai.test1At_of_disjL1
#print axioms Gallai.test2At_of_disjL1
#print axioms Gallai.univTwins_every_path
#print axioms Gallai.not_triangleDisj_of_twins
#print axioms Gallai.disjL1_one_allOdd
#print axioms Gallai.test1At_of_LN_matching
#print axioms Gallai.ForestData2.forM2_odd_all
#print axioms Gallai.ForestData2.evenSet_forM2
#print axioms Gallai.test2At_of_LN_matching
#print axioms Gallai.lN_of_cherryLN
#print axioms Gallai.test1At_of_cherryLN
#print axioms Gallai.test2At_of_cherryLN
#print axioms Gallai.forestLN_far_chain
-- §6: roots without matching data
#print axioms Gallai.PathDecomp.twin_insert
#print axioms Gallai.theta_decomp
#print axioms Gallai.theta_rooted
#print axioms Gallai.test1_fatTheta
#print axioms Gallai.test1At_of_twins
#print axioms Gallai.test2At_of_twins
#print axioms Gallai.fan_single
#print axioms Gallai.fan_root_move
#print axioms Gallai.test1At_of_move1
#print axioms Gallai.test1At_of_move2
#print axioms Gallai.test1At_of_move1'
#print axioms Gallai.test1At_of_move2'
-- §7: certificates, obstructions and star-terminal lifts
#print axioms Gallai.steerK_good
#print axioms Gallai.triangleBase_of_steerK
#print axioms Gallai.test1At_of_steerK
#print axioms Gallai.not_steerK
#print axioms Gallai.not_steerK_triangle
#print axioms Gallai.test1_of_stl
#print axioms Gallai.test2_of_stl2
#print axioms Gallai.gallai_of_stl
#print axioms Gallai.triangleBase_of_E5_E7
#print axioms Gallai.test1_of_lovaszBases
#print axioms Gallai.test1_of_localgirth
#print axioms Gallai.test1_deg_four
