/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.Quadratic.Charts.RatioChartMap
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
/-! # Common homogeneous evaluation for the unchanged quadratic projective charts -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry ProjectiveSpace _root_.MvPolynomial HomogeneousLocalization
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace QuadraticIncidence.InfinityChart
variable (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R]
  {σ : Type u} (g : σ → R)

/-- Evaluation of homogeneous-coordinate polynomials at the monomial functions in the fraction ring.
-/
def homogeneousEvaluation : MvPolynomial (Exponent σ) k →+* FractionRing R :=
  (aeval (fun e => algebraMap R (FractionRing R) (monomialFunction k R g e))).toRingHom

/-- The evaluation homomorphism on the homogeneous localization away from `s`. -/
def homogeneousAwayEvaluation (s : MvPolynomial (Exponent σ) k)
    (hs : homogeneousEvaluation k R g s ≠ 0) :
    Away (homogeneousSubmodule (Exponent σ) k) s →+* FractionRing R :=
  (Localization.awayLift (homogeneousEvaluation k R g) s (isUnit_iff_ne_zero.mpr hs)).comp
    (algebraMap _ (Localization.Away s))

theorem homogeneousAwayEvaluation_mk {s : MvPolynomial (Exponent σ) k} {d : ℕ}
    (hd : s ∈ homogeneousSubmodule (Exponent σ) k d)
    (hs : homogeneousEvaluation k R g s ≠ 0) (n : ℕ)
    (a : MvPolynomial (Exponent σ) k)
    (ha : a ∈ homogeneousSubmodule (Exponent σ) k (n • d)) :
    homogeneousAwayEvaluation k R g s hs (Away.mk _ hd n a ha) =
      homogeneousEvaluation k R g a * (homogeneousEvaluation k R g s)⁻¹ ^ n := by
  change Localization.awayLift (homogeneousEvaluation k R g) s (isUnit_iff_ne_zero.mpr hs)
    (Localization.mk a ⟨s ^ n, n, rfl⟩) = _
  exact Localization.awayLift_mk _ _ _ _ (mul_inv_cancel₀ hs) n

theorem homogeneousEvaluation_X_ne_zero (j : Exponent σ)
    (hj : monomialFunction k R g j ≠ 0) : homogeneousEvaluation k R g (X j) ≠ 0 := by
  simpa [homogeneousEvaluation] using (IsFractionRing.injective R (FractionRing R)).ne hj

theorem nativeDehomogenization_eq_awayEvaluation (j : Exponent σ)
    (hj : monomialFunction k R g j ≠ 0) :
    nativeDehomogenization k R g j = homogeneousAwayEvaluation k R g (X j)
      (homogeneousEvaluation_X_ne_zero k R g j hj) := by
  have hc : (nativeDehomogenization k R g j).comp (polynomialToCoordinateRing k _ j) =
      (homogeneousAwayEvaluation k R g (X j)
        (homogeneousEvaluation_X_ne_zero k R g j hj)).comp
          (polynomialToCoordinateRing k _ j) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, polynomialToCoordinateRing_C,
        nativeDehomogenization_coefficient]
      change _ = homogeneousAwayEvaluation k R g (X j) _
        (Away.mk _ (isHomogeneous_X k j) 0 (C a) (by simp))
      rw [homogeneousAwayEvaluation_mk]
      simp [homogeneousEvaluation]
    · intro e
      simp only [RingHom.comp_apply, polynomialToCoordinateRing_X,
        nativeDehomogenization_ratio k R g j e.val hj]
      change _ = homogeneousAwayEvaluation k R g (X j) _
        (Away.mk _ (isHomogeneous_X k j) 1 (X e.val)
          (by simpa using isHomogeneous_X k e.val))
      rw [homogeneousAwayEvaluation_mk]
      simp [homogeneousEvaluation, ratio, div_eq_mul_inv]
  apply RingHom.ext
  intro z
  have hz : polynomialToCoordinateRing k (Exponent σ) j
      (coordinateRingToPolynomial k (Exponent σ) j z) = z :=
    RingHom.congr_fun
      (polynomialToCoordinateRing_comp_coordinateRingToPolynomial k (Exponent σ) j) z
  simpa only [RingHom.comp_apply, hz] using
    RingHom.congr_fun hc (coordinateRingToPolynomial k (Exponent σ) j z)

/-- The native overlap map is evaluated by the same original homogeneous coordinates. -/
theorem homogeneousAwayEvaluation_awayMap
    {s t : MvPolynomial (Exponent σ) k} {d e : ℕ}
    (hd : s ∈ homogeneousSubmodule (Exponent σ) k d)
    (he : t ∈ homogeneousSubmodule (Exponent σ) k e)
    (hs : homogeneousEvaluation k R g s ≠ 0)
    (ht : homogeneousEvaluation k R g t ≠ 0) :
    (homogeneousAwayEvaluation k R g (s * t) (by simpa using mul_ne_zero hs ht)).comp
      (awayMap (homogeneousSubmodule (Exponent σ) k) he rfl) =
        homogeneousAwayEvaluation k R g s hs := by
  apply RingHom.ext
  intro z
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective
    (homogeneousSubmodule (Exponent σ) k) hd z
  rw [RingHom.comp_apply, homogeneousAwayEvaluation_mk]
  change Localization.awayLift (homogeneousEvaluation k R g) (s * t)
    (isUnit_iff_ne_zero.mpr (by simpa using mul_ne_zero hs ht))
      (awayMap (homogeneousSubmodule (Exponent σ) k) he rfl (Away.mk _ hd n a ha)).val = _
  rw [Away.mk, val_awayMap_mk]
  rw [Localization.awayLift_mk _ _ _ _ (mul_inv_cancel₀ (by simpa using mul_ne_zero hs ht)) n]
  simp only [map_mul, map_pow, mul_inv_rev, mul_pow]
  field_simp [ht, hs]
  rw [mul_assoc, ← mul_pow]
  simp [ht]

/-- Every pivot gives the same actual projective generic point on its product overlap. -/
theorem homogeneousAwayEvaluation_projective_overlap
    {s t : MvPolynomial (Exponent σ) k} {d e : ℕ}
    (hd : s ∈ homogeneousSubmodule (Exponent σ) k d)
    (he : t ∈ homogeneousSubmodule (Exponent σ) k e)
    (hdpos : 0 < d)
    (hs : homogeneousEvaluation k R g s ≠ 0)
    (ht : homogeneousEvaluation k R g t ≠ 0) :
    Spec.map (CommRingCat.ofHom (homogeneousAwayEvaluation k R g s hs)) ≫
        Proj.awayι (homogeneousSubmodule (Exponent σ) k) s hd hdpos =
      Spec.map (CommRingCat.ofHom (homogeneousAwayEvaluation k R g (s * t)
        (by simpa using mul_ne_zero hs ht))) ≫
        Proj.awayι (homogeneousSubmodule (Exponent σ) k) (s * t)
          (SetLike.mul_mem_graded hd he) (hdpos.trans_le (Nat.le_add_right d e)) := by
  rw [← homogeneousAwayEvaluation_awayMap k R g hd he hs ht]
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  rw [Proj.SpecMap_awayMap_awayι]

/-- Native projective evaluation respects equality of the homogeneous pivot. -/
theorem homogeneousAwayEvaluation_projective_congr
    {s t : MvPolynomial (Exponent σ) k} {d e : ℕ}
    (hd : s ∈ homogeneousSubmodule (Exponent σ) k d)
    (he : t ∈ homogeneousSubmodule (Exponent σ) k e)
    (hdpos : 0 < d) (hepos : 0 < e)
    (hs : homogeneousEvaluation k R g s ≠ 0)
    (ht : homogeneousEvaluation k R g t ≠ 0) (h : s = t) (hn : d = e) :
    Spec.map (CommRingCat.ofHom (homogeneousAwayEvaluation k R g s hs)) ≫
        Proj.awayι (homogeneousSubmodule (Exponent σ) k) s hd hdpos =
      Spec.map (CommRingCat.ofHom (homogeneousAwayEvaluation k R g t ht)) ≫
        Proj.awayι (homogeneousSubmodule (Exponent σ) k) t he hepos := by
  subst t
  subst e
  rfl

/-- Nonvanishing original quadratic pivots define one projective generic point. -/
theorem homogeneousAwayEvaluation_projective_eq
    {s t : MvPolynomial (Exponent σ) k} {d e : ℕ}
    (hd : s ∈ homogeneousSubmodule (Exponent σ) k d)
    (he : t ∈ homogeneousSubmodule (Exponent σ) k e)
    (hdpos : 0 < d) (hepos : 0 < e)
    (hs : homogeneousEvaluation k R g s ≠ 0)
    (ht : homogeneousEvaluation k R g t ≠ 0) :
    Spec.map (CommRingCat.ofHom (homogeneousAwayEvaluation k R g s hs)) ≫
        Proj.awayι (homogeneousSubmodule (Exponent σ) k) s hd hdpos =
      Spec.map (CommRingCat.ofHom (homogeneousAwayEvaluation k R g t ht)) ≫
        Proj.awayι (homogeneousSubmodule (Exponent σ) k) t he hepos := by
  rw [homogeneousAwayEvaluation_projective_overlap k R g hd he hdpos hs ht,
    homogeneousAwayEvaluation_projective_overlap k R g he hd hepos ht hs]
  exact homogeneousAwayEvaluation_projective_congr k R g _ _ _ _ _ _
    (mul_comm s t) (Nat.add_comm d e)

end QuadraticIncidence.InfinityChart
