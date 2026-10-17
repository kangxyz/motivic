import Motivic.AlgebraicGeometry.Correspondences.DiagonalZeroCycle

/-! Direct checks of canonical diagonal zeros with their original span maps. -/

set_option linter.hashCommand false
#check Motivic.DiagonalZeroCycle.zeroIdealInclusionIso
#check Motivic.DiagonalZeroCycle.zeroIdealInclusionIso_hom_inclusion
#check Motivic.DiagonalZeroCycle.canonicalSection_zero_graph
#print axioms Motivic.DiagonalZeroCycle.graphCycle_fundamental
#print axioms Motivic.DiagonalZeroCycle.canonicalSection_zero_graph
