import GallaiLean.Test2Lift

/-!
# Audit A37: sanity checks for `GallaiLean/Test2Lift.lean`

1. `#print axioms` for the ten audited theorems (and two helpers).
2. `Test2` (spine) unfolded, and `test2_of_test2At` re-derived by hand.
3. **Non-vacuity**: a concrete Test2 instance of order 6 (J = K_{3,3} + one edge, z = 3, r = 5,
   graph6 `EFzo`) with explicit forest data `L = [(0,5), (4,1), (2,4)]` and an explicit Lovász
   decomposition of `M` satisfying (i) and (ii), so `ForestBase2 J6 3 5` holds and the main
   theorem fires.  This shows `ForestData2`/`ForestBase2` are satisfiable.
-/

open SimpleGraph Gallai

#print axioms Gallai.test2At_of_forestBase2
#print axioms Gallai.test2_of_forestBases2
#print axioms Gallai.floor_of_floorBase
#print axioms Gallai.floor_of_matchingBase
#print axioms Gallai.test2At_of_floor
#print axioms Gallai.test2At_of_floorBase
#print axioms Gallai.test2At_of_disjL1
#print axioms Gallai.test2At_of_pairAvoid
#print axioms Gallai.test2At_of_pair_farApart
#print axioms Gallai.test2At_of_pair_steer2
#print axioms Gallai.append_forest_ends
#print axioms Gallai.test2At_of_leafDecomp

#check @Gallai.Test2
#check @Gallai.test2_of_test2At
#check @Gallai.ForestData2
#check @Gallai.FloorData

namespace A37

/-- The spine's `Test2` is literally the conjunction over roots of `Test2At` (re-derived). -/
example {V : Type} [Fintype V] [DecidableEq V] (J : SimpleGraph V) [DecidableRel J.Adj] (z : V) :
    Test2 J z ↔ ∀ r, J.Adj z r → (∀ v, Even (J.degree v) ↔ v = z ∨ v = r) → Test2At J z r := by
  constructor
  · intro h r hr hev hr'
    exact h r hr' hev
  · intro h r hr hev
    exact h r hr hev hr

/-- Edges of `J6 = K_{3,3} + 35` (graph6 `EFzo`). -/
def edgesL : List (ℕ × ℕ) := [(0,3),(0,4),(0,5),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(3,5)]

def adjB (a b : Fin 6) : Bool :=
  edgesL.any (fun p => (p.1 == a.val && p.2 == b.val) || (p.1 == b.val && p.2 == a.val))

def J6 : SimpleGraph (Fin 6) where
  Adj a b := adjB a b = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance : DecidableRel J6.Adj := fun a b => inferInstanceAs (Decidable (adjB a b = true))

/-- z = 3 and r = 5 are the only even vertices. -/
theorem hev : ∀ v, Even (J6.degree v) ↔ v = 3 ∨ v = 5 := by decide

theorem hr3 : 3 ≤ J6.degree 5 := by decide

abbrev T6 : List (Fin 6) := [0, 1, 2]
abbrev L6 : List (Fin 6 × Fin 6) := [(0, 5), (4, 1), (2, 4)]

/-- The forest data are satisfiable (every field by `decide`). -/
theorem hF : ForestData2 J6 3 5 T6 L6 where
  nodup := by decide
  nbr := by decide
  edge := by decide
  avoid_z := by decide
  r_child := by decide
  children := by decide
  edges := by decide
  parent_first := by decide
  tjoin := by decide

abbrev M6 := forM2 J6 3 T6 L6

theorem a04 : M6.Adj 0 4 := by decide
theorem a15 : M6.Adj 1 5 := by decide
theorem a25 : M6.Adj 2 5 := by decide
theorem a53 : M6.Adj 5 3 := by decide

def P1 : GPath M6 := ⟨0, 4, Walk.cons a04 Walk.nil, (Walk.isPath_def _).mpr (by decide), by decide⟩
def P2 : GPath M6 := ⟨1, 5, Walk.cons a15 Walk.nil, (Walk.isPath_def _).mpr (by decide), by decide⟩
def P3 : GPath M6 := ⟨2, 3, Walk.cons a25 (Walk.cons a53 Walk.nil), (Walk.isPath_def _).mpr (by decide),
  by decide⟩

def D6 : PathDecomp M6 where
  paths := [P1, P2, P3]
  nodup_edges := by decide
  covers := by
    intro e
    induction e using Sym2.ind with
    | h a b =>
      rw [SimpleGraph.mem_edgeSet]
      revert a b
      decide

theorem D6_lovasz : ∀ v, D6.ends v = M6.degree v % 2 := by decide

theorem D6_i : ∀ p ∈ L6, ∀ P ∈ D6.paths, (P.src = p.1 ∨ P.tgt = p.1) → p.2 ∉ P.walk.support := by
  decide

theorem D6_ii : ∀ p ∈ L6, ∀ q ∈ L6, p.1 ≠ q.1 → p.2 = q.2 → ∀ P ∈ D6.paths,
    ¬ ((P.src = p.1 ∨ P.tgt = p.1) ∧ (P.src = q.1 ∨ P.tgt = q.1)) := by
  decide

theorem base6 : ForestBase2 J6 3 5 := ⟨T6, L6, hF, D6, D6_lovasz, D6_i, D6_ii⟩

/-- The main theorem fires on the concrete instance. -/
theorem test2At6 : Test2At J6 3 5 := test2At_of_forestBase2 J6 hev hr3 base6

/-! ### A concrete floor base: `B5 = K_{3,2}` (= `J6 − 3`, relabelled), `w = 0`, `T = [1, 2]`,
`Φ = {13, 32}` rooted at `1`; Lovász decomposition `[3,0,4], [1,4,2]` of `B5 − Φ`. -/

def edgesB : List (ℕ × ℕ) := [(0,3),(0,4),(1,3),(1,4),(2,3),(2,4)]

def adjB5 (a b : Fin 5) : Bool :=
  edgesB.any (fun p => (p.1 == a.val && p.2 == b.val) || (p.1 == b.val && p.2 == a.val))

def B5 : SimpleGraph (Fin 5) where
  Adj a b := adjB5 a b = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance : DecidableRel B5.Adj := fun a b => inferInstanceAs (Decidable (adjB5 a b = true))

theorem hevB : ∀ v, Even (B5.degree v) ↔ v = 0 ∨ v ∈ ([1, 2] : List (Fin 5)) := by decide

abbrev LB : List (Fin 5 × Fin 5) := [(3, 1), (2, 3)]

theorem hFB : FloorData B5 0 [1, 2] LB where
  edge := by decide
  w_not_mem := by decide
  child_ne_w := by decide
  children := by decide
  edges := by decide
  parent_first := by decide
  tjoin := by decide

abbrev K5 := delList B5 (LB.map pairEdge)

theorem b30 : K5.Adj 3 0 := by decide
theorem b04 : K5.Adj 0 4 := by decide
theorem b14 : K5.Adj 1 4 := by decide
theorem b42 : K5.Adj 4 2 := by decide

def Q1 : GPath K5 := ⟨3, 4, Walk.cons b30 (Walk.cons b04 Walk.nil), (Walk.isPath_def _).mpr (by decide),
  by decide⟩
def Q2 : GPath K5 := ⟨1, 2, Walk.cons b14 (Walk.cons b42 Walk.nil), (Walk.isPath_def _).mpr (by decide),
  by decide⟩

def DB : PathDecomp K5 where
  paths := [Q1, Q2]
  nodup_edges := by decide
  covers := by
    intro e
    induction e using Sym2.ind with
    | h a b =>
      rw [SimpleGraph.mem_edgeSet]
      revert a b
      decide

theorem floorBase5 : FloorBase B5 0 [1, 2] :=
  ⟨LB, hFB, DB, by decide, by decide, by decide⟩

/-- The floor lift fires: `p(B5) ≤ 2`. -/
theorem floor5 : ∃ D : PathDecomp B5, D.size ≤ (Fintype.card (Fin 5) - 1) / 2 :=
  floor_of_floorBase B5 hevB floorBase5

end A37

#print axioms A37.test2At6
#print axioms A37.floor5
