/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.AffineTorusPolynomialCycles
public import Lean.Util.CollectAxioms

/-! # Audit of original affine torus generator polynomial cycles -/

@[expose] public noncomputable section

open Motivic.AffineTorusPolynomialPresentation Polynomial

universe u

namespace MotivicTest.AffineTorusPolynomialCycles

variable {k R : Type u} [Field k] [CommRing R] [Algebra k R]
  [IsDomain R] [Algebra.Smooth k R] [IsNoetherianRing R]

/-- The consumer uses the actual original finite-correspondence generator. -/
theorem original_generator_polynomial_cycle (Z : Generator k R) :
    Z.cycle = polynomialCycle (coordinatePolynomial Z) (coordinatePolynomial_monic Z)
      (coordinatePolynomial_constant_isUnit Z) := generator_cycle_eq_polynomialCycle Z

open Lean in
run_cmd do
  for name in #[``polynomialUnit, ``polynomialUnit_val, ``polynomialLaurentMap,
      ``polynomialLaurentMap_closed, ``polynomialProjection, ``polynomialLaurentMap_projection,
      ``polynomialProjection_finite, ``polynomialProjection_flat, ``polynomialInclusion,
      ``polynomialInclusion_closed, ``polynomialInclusion_fst, ``polynomialCycle,
      ``toIntegralCycle_polynomialCycle, ``coordinatePolynomial, ``coordinatePolynomial_monic,
      ``coordinatePolynomial_natDegree_pos, ``polynomialEquiv_symm_coordinate,
      ``polynomialSupportIso, ``supportIsoSpec_inv_map, ``polynomialSupportIso_projection,
      ``polynomialSupportIso_laurentEmbedding, ``polynomialSupportIso_inclusion,
      ``generator_cycle_eq_polynomialCycle, ``original_generator_polynomial_cycle] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original affine polynomial-cycle comparison uses only standard Lean foundations."

end MotivicTest.AffineTorusPolynomialCycles
