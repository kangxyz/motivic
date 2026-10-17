/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.RetainedPrescribedBoundary
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-! # The fixed original quotient and complete new infinity cover the actual bad chart -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurve

/-- The complement of the unchanged original good chart inside the retained open
is covered by the full original quotient, not a reduced replacement. -/
theorem quotient_retained_bad_cover (B : Type u) [CommRing B] (I : Ideal B)
    {N : Scheme.{u}} (i : Spec (.of B) ⟶ N) [IsOpenImmersion i]
    (U : (Spec (.of B)).Opens)
    (hU : (U : Set (Spec (.of B))) = (PrimeSpectrum.zeroLocus (I : Set B))ᶜ)
    (V : N.Opens) (hV : (V : Set N) ⊆ Set.range i) :
    ((V ⊓ i ''ᵁ U : N.Opens) : Set N)ᶜ ⊆
      Set.range (retainedBoundaryInclusion V) ∪
        Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ i) := by
  intro x hx
  by_cases hxV : x ∈ V
  · obtain ⟨y, rfl⟩ := hV hxV
    have hy : y ∈ PrimeSpectrum.zeroLocus (I : Set B) := by
      by_contra hn
      apply hx
      exact ⟨hxV, y, hU.symm ▸ hn, rfl⟩
    have hr : Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) =
        PrimeSpectrum.zeroLocus (I : Set B) := by
      simpa only [Ideal.mk_ker] using
        range_comap_of_surjective (B ⧸ I) (Ideal.Quotient.mk I)
          Ideal.Quotient.mk_surjective
    obtain ⟨z, rfl⟩ := hr.symm ▸ hy
    exact Or.inr ⟨z, rfl⟩
  · exact Or.inl ((range_retainedBoundaryInclusion V).symm ▸ hxV)

end AlgebraicGeometry.Scheme.RelativeCurve
