import Motivic.AlgebraicGeometry.Correspondences.SignedProductPencilEndpoints

/-! Direct checks of the actual signed polynomial family endpoints. -/

set_option linter.hashCommand false
#check Motivic.SignedProductPencilEndpoints.signedCorrespondence
#check Motivic.SignedProductPencilEndpoints.signed_diagonal_zero
#check Motivic.SignedProductPencilEndpoints.signed_one_product
#print axioms Motivic.SignedProductPencilEndpoints.graph_family
#print axioms Motivic.SignedProductPencilEndpoints.signed_diagonal_zero
#print axioms Motivic.SignedProductPencilEndpoints.signed_one_product
#print axioms Motivic.SignedProductPencilEndpoints.signed_one_four_sections
