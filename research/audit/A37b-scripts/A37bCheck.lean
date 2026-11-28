import GallaiLean.Test1AllOdd

/-!
# Audit A37b: sanity checks for `GallaiLean/Test1AllOdd.lean`

1. `#print axioms` for the four headline theorems (and helpers).
2. `Test1` (spine) unfolded against `Test1At`.
3. **Non-vacuity** of `OddData` / `OddBase`:
   (a) `r` a root: `B = C4` (0-1-2-3-0), `T` = all four vertices, `Φ = {01, 23}` as
       `L = [(1,0), (2,3)]` (child, parent), `D₀ = [1 2], [3 0]`.
   (b) `r` a CHILD with two children: `B` on `Fin 6` with edges 01 02 03 04 25 13,
       `T = [0,1,2,3]`, `L = [(0,1), (2,0), (3,0)]` (r = 0 is the child of 1 and the parent of
       2 and 3), `D₀ = [0 4], [2 5], [1 3]`.
   In both, `twoEnds_of_oddBase` fires.
   (c) A genuine Test1 instance through `test1At_of_matchingOdd`: the wheel `W4` on `Fin 5`
       (hub `z = 4`, rim cycle 0-1-2-3-0), `r = 0`, `a₀ = 1`, other pair `(2,3)`,
       `D₀ = [1 2], [3 0]` on `(W4 − z) − {01, 23}`.
-/

open SimpleGraph Gallai

#print axioms Gallai.twoEnds_of_oddBase
#print axioms Gallai.test1At_of_oddBase
#print axioms Gallai.oddBase_of_matching
#print axioms Gallai.test1At_of_matchingOdd

#check @Gallai.OddData
#check @Gallai.OddBase
#check @Gallai.Test1At
#check @Gallai.TriangleDisj

namespace A37b

/-- The spine's `Test1` is the conjunction over roots of `Test1At` (re-derived). -/
example {V : Type} [Fintype V] [DecidableEq V] (J : SimpleGraph V) [DecidableRel J.Adj] (z : V) :
    Test1 J z ↔ ((∀ v, Even (J.degree v) ↔ v = z) → ∀ r, J.Adj z r → Test1At J z r) := by
  constructor
  · intro h hz r _ hr'
    exact h hz r hr'
  · intro h hz r hr
    exact h hz r hr hr

/-! ### (a) r a root: C4 -/

def eC4 : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(0,3)]
def adjC4 (a b : Fin 4) : Bool :=
  eC4.any (fun p => (p.1 == a.val && p.2 == b.val) || (p.1 == b.val && p.2 == a.val))
def C4 : SimpleGraph (Fin 4) where
  Adj a b := adjC4 a b = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩
instance : DecidableRel C4.Adj := fun a b => inferInstanceAs (Decidable (adjC4 a b = true))

abbrev TC : List (Fin 4) := [0, 1, 2, 3]
abbrev LC : List (Fin 4 × Fin 4) := [(1, 0), (2, 3)]

theorem hevC : ∀ v, Even (C4.degree v) ↔ v ∈ TC := by decide

theorem hFC : OddData C4 0 TC LC where
  edge := by decide
  r_mem := by decide
  r_child := by decide
  children := by decide
  edges := by decide
  parent_first := by decide
  tjoin := by decide

abbrev HC := delList C4 (LC.map pairEdge)
theorem c12 : HC.Adj 1 2 := by decide
theorem c30 : HC.Adj 3 0 := by decide
def PC1 : GPath HC := ⟨1, 2, Walk.cons c12 Walk.nil, (Walk.isPath_def _).mpr (by decide), by decide⟩
def PC2 : GPath HC := ⟨3, 0, Walk.cons c30 Walk.nil, (Walk.isPath_def _).mpr (by decide), by decide⟩
def DC : PathDecomp HC where
  paths := [PC1, PC2]
  nodup_edges := by decide
  covers := by
    intro e
    induction e using Sym2.ind with
    | h a b =>
      rw [SimpleGraph.mem_edgeSet]
      revert a b
      decide

theorem baseC : OddBase C4 0 TC := ⟨LC, hFC, DC, by decide, by decide, by decide⟩

theorem liftC : ∃ D : PathDecomp C4, D.size ≤ Fintype.card (Fin 4) / 2 ∧ 2 ≤ D.ends 0 :=
  twoEnds_of_oddBase C4 hevC baseC

/-! ### (b) r a child with two children -/

def e6 : List (ℕ × ℕ) := [(0,1),(0,2),(0,3),(0,4),(2,5),(1,3)]
def adj6 (a b : Fin 6) : Bool :=
  e6.any (fun p => (p.1 == a.val && p.2 == b.val) || (p.1 == b.val && p.2 == a.val))
def B6 : SimpleGraph (Fin 6) where
  Adj a b := adj6 a b = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩
instance : DecidableRel B6.Adj := fun a b => inferInstanceAs (Decidable (adj6 a b = true))

abbrev T6 : List (Fin 6) := [0, 1, 2, 3]
abbrev L6 : List (Fin 6 × Fin 6) := [(0, 1), (2, 0), (3, 0)]

theorem hev6 : ∀ v, Even (B6.degree v) ↔ v ∈ T6 := by decide

theorem hF6 : OddData B6 0 T6 L6 where
  edge := by decide
  r_mem := by decide
  r_child := by decide
  children := by decide
  edges := by decide
  parent_first := by decide
  tjoin := by decide

abbrev H6 := delList B6 (L6.map pairEdge)
theorem h04 : H6.Adj 0 4 := by decide
theorem h25 : H6.Adj 2 5 := by decide
theorem h13 : H6.Adj 1 3 := by decide
def P61 : GPath H6 := ⟨0, 4, Walk.cons h04 Walk.nil, (Walk.isPath_def _).mpr (by decide), by decide⟩
def P62 : GPath H6 := ⟨2, 5, Walk.cons h25 Walk.nil, (Walk.isPath_def _).mpr (by decide), by decide⟩
def P63 : GPath H6 := ⟨1, 3, Walk.cons h13 Walk.nil, (Walk.isPath_def _).mpr (by decide), by decide⟩
def D6 : PathDecomp H6 where
  paths := [P61, P62, P63]
  nodup_edges := by decide
  covers := by
    intro e
    induction e using Sym2.ind with
    | h a b =>
      rw [SimpleGraph.mem_edgeSet]
      revert a b
      decide

theorem base6 : OddBase B6 0 T6 := ⟨L6, hF6, D6, by decide, by decide, by decide⟩

theorem lift6 : ∃ D : PathDecomp B6, D.size ≤ Fintype.card (Fin 6) / 2 ∧ 2 ≤ D.ends 0 :=
  twoEnds_of_oddBase B6 hev6 base6

/-- Negative control: with `r = 0` a child of `1` with only ONE child the data are rejected. -/
theorem not_data_one_child : ¬ OddData B6 0 T6 [(0, 1), (2, 0)] := by
  intro h
  have := h.r_child ⟨(0, 1), by decide, rfl⟩
  revert this
  decide

end A37b

#print axioms A37b.liftC
#print axioms A37b.lift6
