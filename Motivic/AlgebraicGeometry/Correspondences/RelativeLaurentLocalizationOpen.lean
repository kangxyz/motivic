/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.A1.RelativeLaurentGenericOpenZero
public import Mathlib.RingTheory.Localization.Algebra
/-! # Actual base localization identifies the original torus open over D(r) -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.PolynomialOpenQuotient
universe u
namespace Motivic.RelativePolynomialOpenSpans
variable {k R : Type u} [Field k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]
attribute [local instance] away_smooth Polynomial.algebra

/-- Polynomial coefficients localize at the original constant polynomial. -/
theorem polynomial_away (r : R) :
    IsLocalization.Away (C r : R[X]) (Localization.Away r)[X] := by
  simpa only [Submonoid.map_powers] using
    (Polynomial.isLocalization (Submonoid.powers r) (Localization.Away r))

/-- The coefficient localization map is an actual open immersion of the relative lines. -/
theorem lineMap_away_open (r : R) : IsOpenImmersion
    (lineMap (IsScalarTower.toAlgHom k R (Localization.Away r))).left := by
  let : IsLocalization.Away (C r : R[X]) (Localization.Away r)[X] := polynomial_away r
  exact IsOpenImmersion.of_isLocalization (S := (Localization.Away r)[X]) (C r)

/-- Its image is exactly the original base principal open pulled up to the line. -/
theorem lineMap_away_range (r : R) :
    Set.range (lineMap (IsScalarTower.toAlgHom k R (Localization.Away r))).left =
      (principalOpen (C r) : Set (Spec (.of R[X]))) := by
  let : IsLocalization.Away (C r : R[X]) (Localization.Away r)[X] := polynomial_away r
  exact PrimeSpectrum.localization_away_comap_range (Localization.Away r)[X] (C r)

/-- Base localization remains open on the original punctured relative lines. -/
theorem puncturedBaseMap_away_open (r : R) : IsOpenImmersion
    (puncturedBaseMap (IsScalarTower.toAlgHom k R (Localization.Away r))).left := by
  let φ := IsScalarTower.toAlgHom k R (Localization.Away r)
  let : IsOpenImmersion (lineMap φ).left := lineMap_away_open (k := k) r
  have h := openMapOfLE_inclusion φ (principalOpen X) (principalOpen X) (punctured_preimage φ)
  have : IsOpenImmersion ((puncturedBaseMap φ).left ≫ (principalOpen (X : R[X])).ι) := by
    rw [show (puncturedBaseMap φ).left ≫ (principalOpen (X : R[X])).ι =
      (principalOpen (X : (Localization.Away r)[X])).ι ≫ (lineMap φ).left from h]
    infer_instance
  exact IsOpenImmersion.of_comp _ (principalOpen (X : R[X])).ι

/-- The actual structural projection of the original punctured line. -/
def puncturedProjection : (openSite (k := k) (X : R[X])).left ⟶ Spec (.of R) :=
  (principalOpen (X : R[X])).ι ≫ polynomialProjection (.of R)

/-- The output is the original inverse image of the base open, not a chosen replacement. -/
theorem puncturedBaseMap_away_range (r : R) :
    Set.range (puncturedBaseMap (IsScalarTower.toAlgHom k R (Localization.Away r))).left =
      ((puncturedProjection (k := k) (R := R)) ⁻¹ᵁ PrimeSpectrum.basicOpen r :
        Set (openSite (k := k) (X : R[X])).left) := by
  let φ := IsScalarTower.toAlgHom k R (Localization.Away r)
  let b := (puncturedBaseMap φ).left
  have happ (x : (openSite (k := k) (X : (Localization.Away r)[X])).left) :
      (b x).val = (lineMap φ).left x.val :=
    congrArg (fun f => f x)
      (openMapOfLE_inclusion φ (principalOpen X) (principalOpen X) (punctured_preimage φ))
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    have hy : (lineMap φ).left y.val ∈ principalOpen (C r) := by
      exact (congrArg (fun D : Set (Spec (.of R[X])) => (lineMap φ).left y.val ∈ D)
        (lineMap_away_range (k := k) r)).mp ⟨y.val, rfl⟩
    change C r ∉ (b y).val.asIdeal
    rw [happ]
    exact hy
  · intro hx
    have hx' : x.val ∈ principalOpen (C r) := hx
    obtain ⟨y, hy⟩ := (congrArg (fun D : Set (Spec (.of R[X])) => x.val ∈ D)
      (lineMap_away_range (k := k) r)).mpr hx'
    have hyX : y ∈ principalOpen (X : (Localization.Away r)[X]) := by
      have hxx := x.property
      rw [← hy] at hxx
      change (Polynomial.mapRingHom φ.toRingHom) X ∉ y.asIdeal at hxx
      change X ∉ y.asIdeal
      simpa using hxx
    refine ⟨⟨y, hyX⟩, ?_⟩
    apply Subtype.ext
    exact (happ ⟨y, hyX⟩).trans hy

end Motivic.RelativePolynomialOpenSpans
