import GallaiLean.Test1AllOdd

/-! Audit A37b (c): `test1At_of_matchingOdd` fires on the wheel `W4` (hub `z = 4`, rim
0-1-2-3-0), `r = 0`, `a₀ = 1`, other pair `(2,3)`; `D₀ = [1 2], [3 0]` on `(W4 − z) − {01, 23}`. -/

open SimpleGraph Gallai

namespace A37bW

def eW : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(0,3),(0,4),(1,4),(2,4),(3,4)]
def adjW (a b : Fin 5) : Bool :=
  eW.any (fun p => (p.1 == a.val && p.2 == b.val) || (p.1 == b.val && p.2 == a.val))
def W4 : SimpleGraph (Fin 5) where
  Adj a b := adjW a b = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩
instance : DecidableRel W4.Adj := fun a b => inferInstanceAs (Decidable (adjW a b = true))

theorem hz : ∀ v, Even (W4.degree v) ↔ v = 4 := by decide

abbrev S := {v : Fin 5 | v ≠ 4}
def v0 : S := ⟨0, by decide⟩
def v1 : S := ⟨1, by decide⟩
def v2 : S := ⟨2, by decide⟩
def v3 : S := ⟨3, by decide⟩
theorem h04 : (0 : Fin 5) ≠ 4 := by decide

abbrev LP : List (S × S) := [(v1, ⟨0, h04⟩), (v2, v3)]
abbrev Hm := delList (delVert W4 4) (LP.map pairEdge)

theorem hnd : (pairVerts LP).Nodup := by decide
theorem hcover : ∀ v : S, W4.Adj 4 v ↔ v ∈ pairVerts LP := by decide
theorem hedge : ∀ p ∈ LP, (delVert W4 4).Adj p.1 p.2 := by decide

theorem a12 : Hm.Adj v1 v2 := by decide
theorem a30 : Hm.Adj v3 v0 := by decide
def Q1 : GPath Hm := ⟨v1, v2, Walk.cons a12 Walk.nil, (Walk.isPath_def _).mpr (by decide), by decide⟩
def Q2 : GPath Hm := ⟨v3, v0, Walk.cons a30 Walk.nil, (Walk.isPath_def _).mpr (by decide), by decide⟩
def DW : PathDecomp Hm where
  paths := [Q1, Q2]
  nodup_edges := by decide
  covers := by
    intro e
    induction e using Sym2.ind with
    | h a b =>
      rw [SimpleGraph.mem_edgeSet]
      revert a b
      decide

theorem hD : ∀ v, DW.ends v = Hm.degree v % 2 := by decide
theorem hfix : ∀ P ∈ DW.paths, (P.src = v1 ∨ P.tgt = v1) → (⟨0, h04⟩ : S) ∉ P.walk.support := by
  decide
theorem hdisj : TriangleDisj DW [(v2, v3)] := by
  unfold TriangleDisj
  decide

theorem t1 : Test1At W4 4 0 :=
  test1At_of_matchingOdd W4 hz h04 hnd hcover hedge DW hD hfix hdisj

end A37bW

#print axioms A37bW.t1
