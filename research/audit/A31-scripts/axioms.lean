import GallaiLean.RETight
open Gallai
#print axioms Gallai.reassemble
#print axioms Gallai.exists_decomp_of_degStar
#print axioms Gallai.rootedDecomp_of_degStar
#print axioms Gallai.rootedDecomp_of_few_heavy
#print axioms Gallai.rootedDecomp_of_deg_le_six
#check @Gallai.exists_decomp_of_degStar
#check @Gallai.rootedDecomp_of_deg_le_six
#check @Gallai.rootedDecomp_of_few_heavy
#print Gallai.RootedDecomp
#print Gallai.heavyNbrs
#print Gallai.starDel
#print Gallai.evenSet
#check @Gallai.lovasz_ends
-- non-vacuity: the hypotheses are satisfiable (K_4 minus a perfect matching = C_4, k = 2)
example : ∃ (B : SimpleGraph (Fin 4)) (_ : DecidableRel B.Adj), (∀ a, Even (B.degree a)) ∧
    B.degree 0 + 2 = 2 * 2 := by
  refine ⟨SimpleGraph.fromRel (fun a b : Fin 4 => (a.val + b.val) % 2 = 1), inferInstance, ?_, ?_⟩
  · decide
  · decide
