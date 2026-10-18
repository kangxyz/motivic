# Presheaves with transfers: actual contraction

This family constructs contraction from the literal affine-line and Laurent-torus
products over an arbitrary field. Coefficients may live in an independent
universe.

- `ContractionExterior.lean` gives parameter products on signed finite
  correspondences and their action on additive transfer presheaves. Product maps
  of schemes are the existing actual graph correspondences.
- `ContractionGeometry.lean` supplies the polynomial-to-Laurent open immersion,
  the torus unit section, and the actual base-product identification.
- `Contraction.lean` defines contraction as the cokernel of affine-line-to-torus
  restriction. It constructs the quotient transfer action and identifies sections
  with the ordinary quotient by the restriction image.
- `ContractionHI.lean` identifies this quotient, for homotopy-invariant
  coefficients, with the kernel of the actual torus unit restriction.
- `ContractionNaturality.lean` proves coefficient functoriality and naturality of
  the quotient/kernel comparison.
- `ContractionInvariance.lean` proves that actual parameter sections and actual
  contraction preserve ordinary homotopy invariance. The explicit exchange of
  the last two relative-product factors identifies the projection on parameter
  sections with a genuine affine-line projection. The inverse given by the zero
  section descends through the objectwise epimorphic Laurent quotient. The final
  theorem asserts invertibility of the literal projection pullback, not just the
  existence of an abstract isomorphism between section groups.

The consumer checks are `MotivicTest/TransferContraction.lean` and
`MotivicTest/TransferContractionInvariance.lean`. The foundational contraction constructions are separate from the
[canonical boundary/sheaf comparisons](../../Cohomology/A1/ContractionBoundarySheafComparison.lean).
Strict A1 invariance remains open.

[ContractionComplement](ContractionComplement.lean) retains the actual original
complement maps. [NisnevichLocalZero](NisnevichLocalZero.lean) connects genuine
local-zero data with sheafification; it does not assume objectwise exactness
of a sheaf cokernel. The ordinary-cohomology
[Cartier boundary entry](../../Cohomology/A1/CartierBoundary.lean) retains an
explicit Epi input on its original cohomology-presheaf boundary map.
