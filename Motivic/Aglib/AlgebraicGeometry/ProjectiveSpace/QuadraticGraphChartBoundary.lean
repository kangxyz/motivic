/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.QuadraticGraphChartEquations

/-! # The full native graph image chart has empty infinity -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial
universe u
namespace AlgebraicGeometry.Scheme

/-- A unit in the actual schematic image excludes the whole corresponding closed locus. -/
theorem affineImage_preimage_basicOpen_eq_top {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (z : A) (hz : IsUnit (affineImageCoordinateMap φ z)) :
    (Spec.map (CommRingCat.ofHom φ)).imageι ⁻¹ᵁ PrimeSpectrum.basicOpen z = ⊤ := by
  rw [← basicOpen_eq_of_affine (R := .of A) z, preimage_basicOpen_top]
  exact basicOpen_of_isUnit _ hz

end AlgebraicGeometry.Scheme
namespace QuadraticIncidence.InfinityChart
variable (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R]
  {σ : Type u} [Fintype σ] (g : σ → R) (d : ℕ)

/-- Every point of the full native graph image lies in the original non-infinity open. -/
theorem chartGraphImage_no_infinity (j : Exponent σ)
    (hj : monomialFunction k R g j ≠ 0) (c : Fin (d + 1) × Exponent σ → k)
    (hc : NoCommonInfinityZero k R g d c) (x : chartGraphImage k R g d j c) :
    (Spec.map (CommRingCat.ofHom (C : chart k R g j →+*
      MvPolynomial (Fin (d + 1)) (chart k R g j))))
      ((Spec.map (@CommRingCat.ofHom
        (MvPolynomial (Fin (d + 1)) (chart k R g j)) (FractionRing R)
        inferInstance inferInstance (chartGraphEvaluation k R g d j c))).imageι x) ∈
        PrimeSpectrum.basicOpen (infinityCoordinate k R g j) := by
  have H := @Scheme.affineImage_preimage_basicOpen_eq_top
    (MvPolynomial (Fin (d + 1)) (chart k R g j)) (FractionRing R)
    inferInstance inferInstance (chartGraphEvaluation k R g d j c) (C (infinityCoordinate k R g j))
    (chartGraphImage_infinity_isUnit k R g d j hj c hc)
  have hx : x ∈ (Spec.map (@CommRingCat.ofHom
        (MvPolynomial (Fin (d + 1)) (chart k R g j)) (FractionRing R)
        inferInstance inferInstance (chartGraphEvaluation k R g d j c))).imageι ⁻¹ᵁ
      PrimeSpectrum.basicOpen (C (infinityCoordinate k R g j)) := by
    rw [H]
    trivial
  exact hx

end QuadraticIncidence.InfinityChart
