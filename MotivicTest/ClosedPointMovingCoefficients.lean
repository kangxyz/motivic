/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
import Motivic.Aglib.RingTheory.Bertini.ClosedPointMovingCoefficients
import Motivic.Aglib.RingTheory.Bertini.MovingPointCoefficientDimension
import Lean.Util.CollectAxioms

/-! # Actual closed-point coefficients feed the normalized moving-point bound -/

open scoped TensorProduct
open QuadraticIncidence QuadraticIncidence.ClosedPoint

section

variable (k R : Type) [Field k] [CommRing R] [Algebra k R]
  [Algebra.FiniteType k R] (p : PrimeSpectrum R) [p.asIdeal.IsMaximal]

example : Module.Finite k p.asIdeal.ResidueField := residueField_finite k R p

example : Module.Finite R (R ⊗[k] p.asIdeal.ResidueField) := inferInstance

example (n : ℕ) (g : Fin n → R) (i : Fin n) :
    selectedValue k R p (g i) = 1 ⊗ₜ[k] algebraMap R p.asIdeal.ResidueField (g i) := rfl

example (n : ℕ) (g : Fin n → R) (i : Fin n) :
    difference k R p (g i) = algebraMap R (CoefficientRing k R p) (g i) -
      1 ⊗ₜ[k] algebraMap R p.asIdeal.ResidueField (g i) := difference_eq k R p (g i)

example (n : ℕ) (g : Fin n → R) (i : Fin n) :
    diagonalEvaluation k R p (difference k R p (g i)) = 0 :=
  diagonalEvaluation_difference k R p (g i)

example : Ideal.comap (algebraMap R (CoefficientRing k R p))
    (RingHom.ker (diagonalEvaluation k R p).toRingHom) = p.asIdeal :=
  diagonalKernel_comap k R p

example (d : ℕ) (i₀ : Fin d) (r : R) :
    IsUnit (algebraMap (CoefficientRing k R p)
      (MovingPointChart.Ring (CoefficientRing k R p) d i₀ (difference k R p r))
      (algebraMap R (CoefficientRing k R p) r -
        1 ⊗ₜ[k] algebraMap R p.asIdeal.ResidueField r)) :=
  MovingPointChart.difference_isUnit (CoefficientRing k R p) d i₀ (difference k R p r)

example [IsDomain R] (d : ℕ) (i₀ : Fin d) (r : R)
    (E : Type) [Field E] [Algebra k E]
    [Algebra (MovingPointChart.Ring (CoefficientRing k R p) d i₀ (difference k R p r)) E]
    [IsScalarTower k
      (MovingPointChart.Ring (CoefficientRing k R p) d i₀ (difference k R p r)) E]
    (hd : Algebra.trdeg k R = (d + 1 : ℕ)) :
    Algebra.trdeg k
      (IncidenceCoefficientField.field k
        (MovingPointChart.Ring (CoefficientRing k R p) d i₀ (difference k R p r)) E) ≤
      (2 * d : ℕ) :=
  MovingPointChart.trdeg_coefficientField_le_twice k R (CoefficientRing k R p) d i₀
    (difference k R p r) E hd

end

open Lean in
run_cmd do
  for name in #[``residueField_finite, ``coefficientRing_finite,
      ``selectedValue, ``movingValue, ``difference, ``difference_eq,
      ``diagonalEvaluation, ``diagonalEvaluation_tmul,
      ``diagonalEvaluation_selectedValue, ``diagonalEvaluation_movingValue,
      ``diagonalEvaluation_difference, ``difference_mem_diagonalKernel,
      ``diagonalEvaluation_surjective, ``diagonalKernel_comap] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual closed-point moving coefficients: standard foundations only."
