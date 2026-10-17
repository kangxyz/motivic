module

public import Motivic.AlgebraicGeometry.Correspondences.AffineTorusDivisorExact
public import Motivic.Aglib.RingTheory.BoundaryOnePointedExact
public import Motivic.AlgebraicGeometry.Correspondences.IntegralSourceBaseCorrespondences
public import Lean.Util.CollectAxioms

/-! # Direct foundation audit of the actual affine divisor exact sequence -/

open Lean in
run_cmd do
  for name in #[``Motivic.structureCorrespondenceEquiv,
      ``Polynomial.BoundaryOneRationalFunctions.signedValue_kernel_decomposition,
      ``Polynomial.BoundaryOneRationalFunctions.boundary_identityPoint_intersection,
      ``Polynomial.BoundaryOneRationalFunctions.boundaryInvariant,
      ``Polynomial.BoundaryOneRationalFunctions.boundaryInvariant_eq_one_iff,
      ``Polynomial.BoundaryOneRationalFunctions.boundaryInvariant_surjective,
      ``Polynomial.BoundaryOneRationalFunctions.fractionDegree_natural,
      ``Polynomial.BoundaryOneRationalFunctions.signedValueHom_natural,
      ``Motivic.AffineTorusPolynomialPresentation.divisorDegreeUnit,
      ``Motivic.AffineTorusPolynomialPresentation.divisorDegreeUnit_eq_zero_iff,
      ``Motivic.AffineTorusPolynomialPresentation.divisorDegreeUnit_surjective,
      ``Motivic.AffineTorusPolynomialPresentation.divisorDegreeUnit_boundaryDivisor,
      ``Motivic.AffineTorusPolynomialPresentation.boundaryDivisor_injective] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "The original affine divisor exact sequence uses only standard Lean foundations."
