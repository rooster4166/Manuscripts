import GallaiLean.CycleInsert
open Gallai
#print axioms Gallai.rootedDecomp_of_spineTestsNMC
#print axioms Gallai.test1_fullCone_iff
#print axioms Gallai.rootedDecomp_of_gallai
#print axioms Gallai.fullConeTests_iff
#print axioms Gallai.kConnected_three_fullCone_iff
#print axioms Gallai.rootedDecomp_of_dbl
#print axioms Gallai.PathDecomp.cycle_insert
#print axioms Gallai.PathDecomp.ear_insert
#print axioms Gallai.gallai_iff_spineTests'
#check @Gallai.rootedDecomp_of_spineTestsNMC
#check @Gallai.rootedDecomp_iff_addLeaf
#check @Gallai.GPath.exists_orient_src
#check @Gallai.GPath.exists_join
-- sanity: RootedDecomp unfolds as stated
example {W : Type} [Fintype W] [DecidableEq W] (B : SimpleGraph W) (r : W) :
    RootedDecomp B r ↔ ∃ D : PathDecomp B, D.size ≤ Fintype.card W / 2 ∧ 2 ≤ D.ends r := Iff.rfl
