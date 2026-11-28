import GallaiLean.LeafTails
/-! A40: Theorem A fires on a concrete instance (non-vacuity).  G: edges 01, 12, 13, 34, 35 on Fin 6
(all degrees odd); one leaf tail (0, {4}) with 4 at distance three from the leaf 0.
Also Corollary B fires on the same graph with c = 2, a = 4 and the tail (5, {0}). -/
open Gallai SimpleGraph

set_option maxRecDepth 20000

namespace A40

def edgesL : List (ℕ × ℕ) := [(0,1), (1,2), (1,3), (3,4), (3,5)]

def adjB (a b : Fin 6) : Bool :=
  edgesL.any (fun p => (p.1 == a.val && p.2 == b.val) || (p.1 == b.val && p.2 == a.val))

def G6 : SimpleGraph (Fin 6) where
  Adj a b := adjB a b = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance : DecidableRel G6.Adj := fun a b => inferInstanceAs (Decidable (adjB a b = true))

def T6 : Finset (Fin 6 × Finset (Fin 6)) := {((0 : Fin 6), {(4 : Fin 6)})}

theorem ev6 : (evenSet G6).card ≤ 1 := by decide
theorem lt6 : LeafTails G6 T6 := by unfold LeafTails FarApart T6; decide
theorem sp6 : SparseIn G6 (heads T6) := by unfold SparseIn heads T6; decide

theorem thmA6 : ∃ D : PathDecomp G6, (∀ v, D.ends v = G6.degree v % 2) ∧ KeepsTails D T6 :=
  leaf_tails G6 ev6 lt6 sp6

def T6b : Finset (Fin 6 × Finset (Fin 6)) := {((5 : Fin 6), {(0 : Fin 6)})}
theorem ev6b : (evenSet G6).card = 0 := by decide
theorem lt6b : LeafTails G6 T6b := by unfold LeafTails FarApart T6b; decide
theorem sp6b : SparseIn G6 (insert 4 (heads T6b)) := by unfold SparseIn heads T6b; decide

theorem corB6 : ∃ D : PathDecomp G6, (∀ v, D.ends v = G6.degree v % 2) ∧
    (∀ P ∈ D.paths, (P.src = 2 ∨ P.tgt = 2) → (4 : Fin 6) ∉ P.walk.support) ∧ KeepsTails D T6b :=
  lovasz_avoid_leafTails G6 ev6b (c := 2) (a := 4) (by decide) (by decide) (by decide) lt6b
    (by unfold T6b; decide) sp6b

end A40
#print axioms A40.thmA6
#print axioms A40.corB6
