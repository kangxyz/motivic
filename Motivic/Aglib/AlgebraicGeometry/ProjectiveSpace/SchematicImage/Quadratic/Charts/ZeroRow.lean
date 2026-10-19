/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.Quadratic.Charts.GraphChartEquations
public import Motivic.Aglib.RingTheory.Bertini.AuxiliaryQuadraticParameter
/-! # A zero auxiliary row preserves the original tuple, including zero-dimensional targets -/
@[expose] public noncomputable section
open _root_.MvPolynomial
universe u
namespace QuadraticIncidence.InfinityChart
variable (k R : Type u) [Field k] [CommRing R] [Algebra k R]
  {σ : Type u} [Fintype σ] (g : σ → R) (d : ℕ)

/-- The unchanged original coordinate map with any number of rows. -/
def quadraticCoordinateHom (c : Fin d × Exponent σ → k) :
    MvPolynomial (Fin d) k →+* R :=
  (aeval (fun i => aeval g (parameterTuple k σ d c i).val)).toRingHom

theorem originalFunction_eq_sum_rows (c : Fin d × Exponent σ → k) (i : Fin d) :
    aeval g (parameterTuple k σ d c i).val =
      ∑ e, algebraMap k R (c (i, e)) * monomialFunction k R g e := by
  classical
  simp only [parameterTuple, Finset.sum_apply, Pi.smul_apply,
    parameterBasis_apply, Pi.single_apply, Fintype.sum_prod_type]
  simp [monomialBasis_coe, monomialFunction, Algebra.smul_def]

/-- Forget only the identically zero auxiliary coordinate; all original rows remain literal. -/
def eraseZeroRow : MvPolynomial (Fin (d + 1)) k →+* MvPolynomial (Fin d) k :=
  (aeval (Fin.cases 0 (fun i => X i))).toRingHom

theorem quadraticCoordinateHom_prepend_zero (c : Fin d × Exponent σ → k) :
    quadraticCoordinateHom k R g (d + 1) (prependParameters k d 0 c) =
      (quadraticCoordinateHom k R g d c).comp (eraseZeroRow k d) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [quadraticCoordinateHom, eraseZeroRow]
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [quadraticCoordinateHom, eraseZeroRow, originalFunction_eq_sum_rows,
        prependParameters]
    · simp [quadraticCoordinateHom, eraseZeroRow, originalFunction_eq_sum_rows,
        prependParameters]

variable [IsDomain R]
omit [Fintype σ] in
/-- Padding a zero row changes no common-zero condition, even when d is zero. -/
theorem noCommonInfinityZero_prepend_zero [Finite σ] (c : Fin d × Exponent σ → k)
    (h : ∀ j : Exponent σ, monomialFunction k R g j ≠ 0 →
      ∀ (K : Type u) [Field K] [Algebra k K] [Algebra (boundaryRing k R g j) K]
        [IsScalarTower k (boundaryRing k R g j) K],
        ¬ ProjectiveEvaluationIncidence.Vanishes k (boundaryRing k R g j) K
          (boundaryCoordinate k R g j) d c) :
    NoCommonInfinityZero k R g d (prependParameters k d 0 c) := by
  intro j hj
  dsimp only
  intro K hK hk hA ht hv
  let : Field K := hK
  let : Algebra k K := hk
  let : Algebra (boundaryRing k R g j) K := hA
  let : IsScalarTower k (boundaryRing k R g j) K := ht
  apply h j hj K
  intro i
  simpa only [prependParameters, Fin.cases_succ] using hv i.succ

end QuadraticIncidence.InfinityChart
