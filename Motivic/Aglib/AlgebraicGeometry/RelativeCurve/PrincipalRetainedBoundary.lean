/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.RetainedBoundaryPrescribedScheme

/-! # An actual principal base shrink keeps the affine retained curve and full prescribed scheme -/
@[expose] public noncomputable section
open CategoryTheory
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurve

/-- The final base shrink can be principal; its retained curve stays affine,
and the entire original prescribed finite scheme is retained over that same base. -/
theorem exists_principal_finite_retainedBoundary_preserving_scheme
    (R : Type u) [CommRing R] {C B Z : Scheme.{u}}
    (q : C ⟶ Spec (CommRingCat.of R)) [IsProper q] (b : B ⟶ C)
    [IsFinite (b ≫ q)] (U V : C.Opens) [IsAffine V.toScheme]
    (hboundary : (U : Set C)ᶜ ⊆ Set.range b) (s : Spec (CommRingCat.of R))
    (hwhole : ∀ x : C, q x = s → x ∈ U → x ∈ V)
    (z : Z ⟶ C) [IsFinite (z ≫ q)] (hzU : Set.range z ⊆ U) :
    ∃ r : R, s ∈ PrimeSpectrum.basicOpen r ∧
      IsFinite ((retainedBoundaryInclusion V ≫ q) ∣_ PrimeSpectrum.basicOpen r) ∧
      IsAffine (((V.ι ≫ q) ⁻¹ᵁ PrimeSpectrum.basicOpen r).toScheme) ∧
      ∀ x : Z, (z ≫ q) x ∈ PrimeSpectrum.basicOpen r → z x ∈ V := by
  obtain ⟨T, hs, hfinite, hZ⟩ := exists_finite_retainedBoundary_preserving_scheme
    q b U V hboundary s hwhole z hzU
  obtain ⟨_, ⟨_, ⟨r : R, rfl⟩, rfl⟩, hsr, hrT⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hs T.isOpen
  have : IsFinite ((retainedBoundaryInclusion V ≫ q) ∣_ T) := hfinite
  have : IsAffine (Scheme.Opens.toScheme (X := Spec (.of R)) (PrimeSpectrum.basicOpen r)) :=
    IsAffine.of_isIso (basicOpenIsoSpecAway (R := .of R) r).hom
  refine ⟨r, hsr, finite_morphismRestrict_of_le _ hrT, ?_, fun x hx => hZ x (hrT hx)⟩
  exact IsAffineOpen.preimage (by assumption) (V.ι ≫ q)

end AlgebraicGeometry.Scheme.RelativeCurve
