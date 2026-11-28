import GallaiLean.DenseRoot

open Gallai SimpleGraph

/-- C4 on Fin 4: 0-1-2-3-0, root 0 (k = 2). -/
def C4 : SimpleGraph (Fin 4) := SimpleGraph.fromRel (fun a b : Fin 4 => (a.val + 1) % 4 = b.val)

instance : DecidableRel C4.Adj := fun a b => by unfold C4; infer_instance

example : ∃ D : PathDecomp C4, D.size = 2 ∧ D.ends 0 = 2 :=
  exists_decomp_of_oneEven C4 (k := 2) le_rfl (by decide) 0 (by decide) (by decide) (by decide) 0
    (by decide) (by intro t h1 h2; omega)
