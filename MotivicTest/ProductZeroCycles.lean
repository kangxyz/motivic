module
import Motivic.AlgebraicGeometry.Correspondences.ProductZeroCycles
/-! Direct checks of full product zero-cycle multiplicities and span maps. -/

set_option linter.hashCommand false

#check Motivic.ProductZeroCycles.coefficient_and_finiteness
#check Motivic.ProductZeroCycles.coefficient_zero
#check Motivic.ProductZeroCycles.fundamentalCycle_product
#check Motivic.ProductZeroCycles.ofFiniteFlatSpan_product
#print axioms Motivic.ProductZeroCycles.ofFiniteFlatSpan_product
#check Motivic.ProductZeroCycles.ofFiniteFlatSpan_productSection
#print axioms Motivic.ProductZeroCycles.ofFiniteFlatSpan_productSection
