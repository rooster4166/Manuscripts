import GallaiLean.TRN
import GallaiLean.NeighbourAvoid
open Gallai
#print axioms Gallai.avoid_of_separating_child
#print axioms Gallai.avoid_of_farApart
#print axioms Gallai.avoid_of_degTwo_indep
#print axioms Gallai.tightTransferNCore_of
#print axioms Gallai.conjN_of_core
#print axioms Gallai.conjN_of_core_neighbourAvoid
#print axioms Gallai.fan_single_supp
#print axioms Gallai.l1_tight_transfer
#check @Gallai.fan_single_supp
#check @Gallai.separation
#check @Gallai.lovasz_avoid_nonadj
#check @Gallai.avoid_free_target
#check @Gallai.avoid_of_splitOff
#check @Gallai.l1_tight_transfer
#print Gallai.TightTransferNCore
#print Gallai.ConjNBelow

-- With NA now proved (GallaiLean.NeighbourAvoid, merged during this audit), the core alone gives N.
section
variable {V : Type} [Fintype V] [DecidableEq V]
theorem audit_conjN_of_core_alone (hT : Gallai.TightTransferNCore V) : Gallai.ConjNOn V :=
  Gallai.conjN_of_core_neighbourAvoid hT Gallai.neighbourAvoidOn
end
#print axioms audit_conjN_of_core_alone
