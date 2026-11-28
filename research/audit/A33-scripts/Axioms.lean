import GallaiLean.NeighbourAvoid
open Gallai
#print axioms Gallai.neighbourAvoidOn
#print axioms Gallai.neighbourAvoid
#print axioms Gallai.avoid_packed_of_reach
#print axioms Gallai.avoid_of_reach
#print axioms Gallai.avoid_iff_reach
#print axioms Gallai.mem_pathEndingAt_of_component_sub
#print axioms Gallai.meets_of_component_sub
#print axioms Gallai.avoid_packed_iff_reach
#print axioms Gallai.conjNDegTwoOn
#print axioms Gallai.conjN_of_tightTransferN
#print axioms Gallai.conjN_of_TR
#print axioms Gallai.steer_meetsOnce
#print axioms Gallai.steer_of_inv
#print axioms Gallai.exists_inv_subgraph
#print axioms Gallai.exists_toggle_walk
#print axioms Gallai.fan_step_meetsOnce
#print axioms Gallai.apexSep_meetsOnce
#check @Gallai.neighbourAvoidOn
#check @Gallai.conjN_of_TR
#check @Gallai.conjN_of_tightTransferN
#check @Gallai.conjNDegTwoOn
#print Gallai.NeighbourAvoidOn
-- sanity: the hypotheses are satisfiable (non-vacuity), e.g. TightTransferNOn is not provably False here;
-- check that the statement types are as expected
example : ∀ (V : Type) [Fintype V] [DecidableEq V], Gallai.NeighbourAvoidOn V := fun V _ _ => Gallai.neighbourAvoidOn
