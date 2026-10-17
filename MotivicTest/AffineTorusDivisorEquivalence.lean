/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.AffineTorusDivisorEquivalence
public import Lean.Util.CollectAxioms

/-! # Direct audit of the original affine correspondence divisor equivalence -/

@[expose] public noncomputable section

open Motivic Motivic.AffineTorusPolynomialPresentation Polynomial.BoundaryOneRationalFunctions
open Polynomial AlgebraicGeometry AlgebraicGeometry.Scheme.PolynomialLaurent

universe u

namespace MotivicTest.AffineTorusDivisorEquivalence

variable {k R : Type u} [Field k] [CommRing R] [Algebra k R]
  [IsDomain R] [Algebra.Smooth k R] [IsNoetherianRing R]

def actual_divisor_equivalence : Additive (admissibleGroup R) ≃+
    FiniteCorrespondence (baseMap k R) (laurentProjection (.of k)) :=
  rationalDivisorEquiv

theorem actual_boundary_divisor_injective :
    Function.Injective (boundaryDivisor (k := k) (R := R)) :=
  boundaryDivisor_injective

open Lean in
run_cmd do
  for name in #[``primePolynomialGenerator, ``primePolynomialGenerator_ideal,
      ``primePolynomialSupportIso, ``primePolynomialSupportIso_inclusion,
      ``polynomialCycle_eq_primeGenerator, ``primePolynomialSupportIso_laurentEmbedding,
      ``primePolynomialGenerator_eq_kernel, ``dvd_of_polynomialLaurentMap_kernel_le,
      ``primePolynomialGenerator_injective, ``coordinatePolynomial_prime,
      ``generator_eq_primePolynomialGenerator, ``coordinatePolynomial_primePolynomialGenerator,
      ``cycleRationalFunction, ``cycleRationalFunction_single, ``cycleRationalFunction_cycle,
      ``rationalDivisorHom_cycleRationalFunction,
      ``generatorRationalFunction_primePolynomialGenerator,
      ``cycleRationalFunction_denominator_prime, ``cycleRationalFunction_denominator_prod,
      ``exists_prime_denominator_factors, ``cycleRationalFunction_denominator,
      ``cycleRationalFunction_rationalDivisorHom, ``rationalDivisorEquiv,
      ``boundaryDivisor_injective, ``actual_divisor_equivalence,
      ``actual_boundary_divisor_injective] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual affine divisor equivalence uses only standard Lean foundations."

end MotivicTest.AffineTorusDivisorEquivalence
