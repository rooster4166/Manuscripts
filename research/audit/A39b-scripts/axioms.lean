import GallaiLean.DenseRootB

/-! Audit A39b: axioms and exact signatures of the headline declarations of `DenseRootB.lean`. -/

open Gallai

#print axioms Gallai.consPath
#print axioms Gallai.consPath_length
#print axioms Gallai.GPath.liftLe
#print axioms Gallai.exists_lovasz_connector
#print axioms Gallai.connector_core
#print axioms Gallai.exists_decomp_of_connector
#print axioms Gallai.exists_decomp_of_connector_mid
#print axioms Gallai.test1At_of_connector
#print axioms Gallai.test1At_of_connector_mid

set_option pp.proofs false
#check @Gallai.consPath
#check @Gallai.exists_lovasz_connector
#check @Gallai.connector_core
#check @Gallai.exists_decomp_of_connector
#check @Gallai.exists_decomp_of_connector_mid
#check @Gallai.test1At_of_connector
#check @Gallai.test1At_of_connector_mid
#print Gallai.Test1At
#print Gallai.delVert
#print Gallai.delList
#print Gallai.heavyNbrs
#print Gallai.GPath.endsAt
#print Gallai.PathDecomp.ends
