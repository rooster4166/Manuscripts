import GallaiLean.DenseRootB
/-! Audit A39b sanity check: this file must FAIL to compile (`decide` rejects a false count),
showing that the `decide` proofs in `nonvacuous.lean` are really evaluated. -/
open Gallai SimpleGraph Finset
/-- A graph on `Fin n` from an edge list. -/
def gr (n : ℕ) (L : List (ℕ × ℕ)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun a b : Fin n => (a.val, b.val) ∈ L)

instance (n : ℕ) (L : List (ℕ × ℕ)) : DecidableRel (gr n L).Adj := fun a b => by
  unfold gr; infer_instance

/-! ### 1. `δ = 0`, `k = 2`: `B = K₄ − rs`, `r = 0`, `s = 3`, `Q = 1 2`. (t-range empty.) -/

def B4 : SimpleGraph (Fin 4) := gr 4 [(0,1),(0,2),(1,2),(1,3),(2,3)]
instance : DecidableRel B4.Adj := by unfold B4; infer_instance

def Q4 : GPath (starDel B4 0) :=
  ⟨1, 2, Walk.cons (by decide) Walk.nil, (Walk.isPath_def _).mpr (by decide), by decide⟩

theorem nv_d0_k2 : ∃ D : PathDecomp B4, D.size = 2 ∧ D.ends 0 = 2 :=
  exists_decomp_of_connector B4 (k := 2) le_rfl (by decide) 0 (by decide) Q4 (by decide)
    (by decide) (by decide) (by decide) 2 (by decide) (by intro t h1 h2; omega)

/-! ### 2. `δ = 0`, `k = 4` (t = 3 is in range, and the condition is tight).
`r = 0`, `N = {1,…,6}`, `s = 7`, `Q = 1 2`; in `B`: `d(3) = d(4) = d(5) = 6`, so `h̃₃ = 3`,
`λ = ⌈3/2⌉ + ⌈3/2⌉ = 4 ≥ 3`, and `⌊3/2⌋ + 1 + 3 = 5 ≤ k + 1`. -/

def B8 : SimpleGraph (Fin 8) := gr 8
  [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),
   (1,2),
   (3,4),(3,5),(4,5),(3,1),(3,2),(3,6),(4,1),(4,2),(4,7),(5,6),(5,7),(5,1),(2,6)]
instance : DecidableRel B8.Adj := by unfold B8; infer_instance

def Q8 : GPath (starDel B8 0) :=
  ⟨1, 2, Walk.cons (by decide) Walk.nil, (Walk.isPath_def _).mpr (by decide), by decide⟩

-- the numbers in the comment
theorem nv_h3 : #((heavyNbrs B8 0 3).filter (fun x => x ∉ Q8.walk.support)) = 3 := by decide
theorem nv_lam : ∑ v ∈ Q8.walk.support.toFinset,
    ((delList (starDel B8 0) Q8.edges).degree v + 1) / 2 = 4 := by decide

theorem nv_d0_k4 : ∃ D : PathDecomp B8, D.size = 4 ∧ D.ends 0 = 2 :=
  exists_decomp_of_connector B8 (k := 4) (by decide) (by decide) 0 (by decide) Q8 (by decide)
    (by decide) (by decide) (by decide) 4 (by decide) (by
      intro t h1 h2
      obtain rfl : t = 3 := by omega
      left; decide)


/-- expected to FAIL: `h̃₃ = 3`, not `4`. -/
example : #((heavyNbrs B8 0 3).filter (fun x => x ∉ Q8.walk.support)) = 4 := by decide
