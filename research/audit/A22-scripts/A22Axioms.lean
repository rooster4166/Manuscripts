import GallaiLean.TerminalMatching
open Gallai
#print axioms Gallai.walk_back
#print axioms Gallai.sep_sparse_fix
#print axioms Gallai.baseG_parity
#print axioms Gallai.ptm2_of_base
#print axioms Gallai.ptm2_of_sparse
#print axioms Gallai.ptm2_girth_core
#print axioms Gallai.ptm2_girth5
#print axioms Gallai.stl_of_ptm2
#print axioms Gallai.stl_of_girth5
#print axioms Gallai.test1_of_girth5
#print axioms Gallai.test1_of_stl
#print Gallai.PTM2At
#print Gallai.NoTriangle
#print Gallai.NoSquare
#print Gallai.STL
#print Gallai.StarAt
#print Gallai.LongAt
#print Gallai.HasShortShort
#print Gallai.Test1
#print Gallai.SparseFam
-- sanity: the hypotheses of ptm2_girth5 are satisfiable on a concrete graph is not needed;
-- check the definitions reduce as expected on a toy example (K2 has no triangle)
example : NoTriangle (⊥ : SimpleGraph (Fin 3)) := fun _ _ _ h _ _ => h
