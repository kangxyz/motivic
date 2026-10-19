/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Bertini.QuadraticInfinityCharts
public import Aglib.AlgebraicGeometry.ProjectiveSpace.CoordinateRing
public import Mathlib.RingTheory.Ideal.Quotient.Operations
/-! # The literal quadratic dehomogenization map and its ratio algebra

The native projective chart map evaluates every coordinate at the unchanged monomial ratio.
Its actual image is the ratio algebra used in the infinity dimension argument.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.MvPolynomial AlgebraicGeometry ProjectiveSpace
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace QuadraticIncidence.InfinityChart
variable (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R]
  {σ : Type u} (g : σ → R) (j : Exponent σ)

/-- The original coordinate polynomials on the `j`-chart evaluate at the actual ratios. -/
def dehomogenizedEvaluation : MvPolynomial {e : Exponent σ // e ≠ j} k →ₐ[k] FractionRing R :=
  aeval (fun e => ratio k R g j e.val)

theorem dehomogenizedEvaluation_range (hj : monomialFunction k R g j ≠ 0) :
    (dehomogenizedEvaluation k R g j).range = chart k R g j := by
  rw [dehomogenizedEvaluation, aeval_range, chart_eq_adjoin_ratios]
  apply le_antisymm
  · apply Algebra.adjoin_mono
    rintro _ ⟨e, rfl⟩
    exact ⟨e.val, rfl⟩
  · apply Algebra.adjoin_le
    rintro _ ⟨e, rfl⟩
    by_cases he : e = j
    · subst e
      rw [ratio_self k R g j hj]
      exact one_mem _
    · exact Algebra.subset_adjoin ⟨⟨e, he⟩, rfl⟩

/-- Evaluation of the native degree-zero homogeneous localization, not an abstract
isomorphic polynomial ring chosen independently of the original coordinates. -/
def nativeDehomogenization : coordinateRing k (Exponent σ) j →+* FractionRing R :=
  (dehomogenizedEvaluation k R g j).toRingHom.comp
    (coordinateRingEquivPolynomial k (Exponent σ) j).toRingHom

@[simp]
theorem nativeDehomogenization_coefficient (a : k) :
    nativeDehomogenization k R g j (coordinateRingCoefficient k (Exponent σ) j a) =
      algebraMap k (FractionRing R) a := by
  simp [nativeDehomogenization, dehomogenizedEvaluation,
    coordinateRingEquivPolynomial, coordinateRingToPolynomial_coefficient]

@[simp]
theorem nativeDehomogenization_ratio (e : Exponent σ)
    (hj : monomialFunction k R g j ≠ 0) :
    nativeDehomogenization k R g j (coordinateRatio k (Exponent σ) j e) =
      ratio k R g j e := by
  by_cases he : e = j
  · subst e
    simp [ratio_self k R g j hj]
  · change dehomogenizedEvaluation k R g j
      (coordinateRingToPolynomial k (Exponent σ) j
        (coordinateRatio k (Exponent σ) j e)) = _
    rw [coordinateRingToPolynomial_ratio k (Exponent σ) j ⟨e, he⟩]
    exact aeval_X _ _

theorem nativeDehomogenization_range (hj : monomialFunction k R g j ≠ 0) :
    (nativeDehomogenization k R g j).range = (chart k R g j).toSubring := by
  ext x
  change (∃ a, nativeDehomogenization k R g j a = x) ↔ x ∈ chart k R g j
  rw [← dehomogenizedEvaluation_range k R g j hj]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨coordinateRingEquivPolynomial k (Exponent σ) j a, rfl⟩
  · rintro ⟨a, rfl⟩
    refine ⟨(coordinateRingEquivPolynomial k (Exponent σ) j).symm a, ?_⟩
    simp [nativeDehomogenization]

/-- The actual quotient by the chart map's kernel is the original ratio algebra. -/
def nativeDehomogenizationQuotientEquiv (hj : monomialFunction k R g j ≠ 0) :
    coordinateRing k (Exponent σ) j ⧸ RingHom.ker (nativeDehomogenization k R g j) ≃+*
      chart k R g j :=
  (nativeDehomogenization k R g j).quotientKerEquivRange.trans
    (RingEquiv.subringCongr (nativeDehomogenization_range k R g j hj))
end QuadraticIncidence.InfinityChart
