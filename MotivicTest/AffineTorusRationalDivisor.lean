/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.AffineTorusRationalDivisor
public import Lean.Util.CollectAxioms

/-! # Direct audit of actual product divisors and the original correspondence map -/

@[expose] public noncomputable section

open Motivic.AffineTorusPolynomialPresentation Polynomial.BoundaryOneRationalFunctions
open Polynomial

universe u

namespace MotivicTest.AffineTorusRationalDivisor

variable {k R : Type u} [Field k] [CommRing R] [Algebra k R]
  [IsDomain R] [IsNoetherianRing R]

theorem actual_product_cycle (p q : R[X]) (hp : p.Monic) (hq : q.Monic)
    (hp0 : IsUnit (p.coeff 0)) (hq0 : IsUnit (q.coeff 0)) :
    polynomialCycle (k := k) (p * q) (hp.mul hq) (by simpa using hp0.mul hq0) =
      polynomialCycle (k := k) p hp hp0 + polynomialCycle (k := k) q hq hq0 :=
  polynomialCycle_mul p q hp hq hp0 hq0

theorem actual_divisor_surjective [Algebra.Smooth k R] :
    Function.Surjective (rationalDivisorHom (k := k) (R := R)) :=
  rationalDivisorHom_surjective

open Lean in
run_cmd do
  for name in #[``polynomialLaurent_eval_toLaurent, ``polynomialLaurent_eval_kernel,
      ``polynomialLaurentMap_kernel_top, ``polynomialGerm, ``polynomialLaurentMap_kernel_stalk,
      ``polynomialGerm_mul, ``polynomialGerm_regular, ``polynomialCycle_mul, ``polynomialCycle_one,
      ``admissibleGroup, ``admissibleFraction, ``admissibleFraction_self,
      ``admissibleFraction_mul, ``boundaryInclusion, ``denominatorCycle, ``denominatorCycle_one,
      ``denominatorCycle_mul, ``divisor_presentation_independent, ``exists_divisor,
      ``rationalDivisor, ``rationalDivisor_eq, ``rationalDivisor_fraction, ``rationalDivisor_one,
      ``rationalDivisor_mul, ``rationalDivisorHom, ``boundaryDivisor, ``generatorRationalFunction,
      ``rationalDivisor_generator, ``rationalDivisorHom_surjective, ``actual_product_cycle,
      ``actual_divisor_surjective] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual product divisors and surjectivity use only standard Lean foundations."

end MotivicTest.AffineTorusRationalDivisor
