/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import MotivicTest.FiniteOpenCoverGluing
public import Motivic.AlgebraicGeometry.Modules.FiniteOpenCoverGluingRecoveryMap

/-!
# Covering recovery and distinct three-open consumers

The finite canonical equalizer recovers the original sheaf using the actual
covering proof. The rational affine-line example has three distinct members
and an inhabited triple intersection.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.MotivicTest.FiniteOpenCoverGluing

open Scheme.Modules Motivic.FiniteOpenModuleGluing

variable (R : CommRingCat.{0}) (r : R)

/-- The third actual affine member is the intersection of the first two. -/
theorem third_is_overlap : threeOpens R r 2 = threeOpens R r 0 ⊓ threeOpens R r 1 := by
  simp [threeOpens, PrimeSpectrum.basicOpen_mul]
  rfl

/-- The actual finite cover recovers the original structure module globally. -/
def threeCanonicalRecoveryIso :
    structureModule R ≅
      glued (threeOpens R r) (localModules R r)
        (canonicalDatum (threeOpens R r) (structureModule R)) :=
  canonicalRecoveryIso (threeOpens R r) (structureModule R) (threeOpens_cover R r)

/-- Evaluation at a rational number gives an actual point of the rational affine line. -/
def polynomialPoint (q : ℚ) : PrimeSpectrum (Polynomial ℚ) :=
  PrimeSpectrum.comap (Polynomial.evalRingHom q) ⟨⊥, inferInstance⟩

/-- Membership in a principal open is the literal nonvanishing evaluation condition. -/
theorem polynomialPoint_mem_basicOpen (q : ℚ) (p : Polynomial ℚ) :
    polynomialPoint q ∈ PrimeSpectrum.basicOpen p ↔ Polynomial.eval q p ≠ 0 := by
  simp [polynomialPoint, PrimeSpectrum.mem_basicOpen]

/-- The three affine-line opens are pairwise distinct; this is a genuine three-open cover. -/
theorem polynomial_three_distinct :
    threeOpens rationalPolynomialRing Polynomial.X 0 ≠
        threeOpens rationalPolynomialRing Polynomial.X 1 ∧
      threeOpens rationalPolynomialRing Polynomial.X 0 ≠
        threeOpens rationalPolynomialRing Polynomial.X 2 ∧
      threeOpens rationalPolynomialRing Polynomial.X 1 ≠
        threeOpens rationalPolynomialRing Polynomial.X 2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hh := congrArg (fun V : (Spec rationalPolynomialRing).Opens => polynomialPoint 0 ∈ V) h
    change (Polynomial.eval 0 Polynomial.X ≠ 0) =
      (Polynomial.eval 0 (1 - Polynomial.X) ≠ 0) at hh
    simp [Polynomial.eval_sub] at hh
  · intro h
    have hh := congrArg (fun V : (Spec rationalPolynomialRing).Opens => polynomialPoint 1 ∈ V) h
    change (Polynomial.eval 1 Polynomial.X ≠ 0) =
      (Polynomial.eval 1 (Polynomial.X * (1 - Polynomial.X)) ≠ 0) at hh
    simp [Polynomial.eval_sub, Polynomial.eval_mul] at hh
  · intro h
    have hh := congrArg (fun V : (Spec rationalPolynomialRing).Opens => polynomialPoint 0 ∈ V) h
    change (Polynomial.eval 0 (1 - Polynomial.X) ≠ 0) =
      (Polynomial.eval 0 (Polynomial.X * (1 - Polynomial.X)) ≠ 0) at hh
    simp [Polynomial.eval_sub, Polynomial.eval_mul] at hh

/-- The actual triple intersection is inhabited, so the triple cocycle is not vacuous. -/
theorem polynomial_triple_nonempty : Nonempty
    ↥(threeOpens rationalPolynomialRing Polynomial.X 0 ⊓
      threeOpens rationalPolynomialRing Polynomial.X 1 ⊓
        threeOpens rationalPolynomialRing Polynomial.X 2) := by
  rw [← third_is_overlap, inf_idem, third_is_overlap]
  exact polynomial_overlap_nonempty

end Motivic.MotivicTest.FiniteOpenCoverGluing
