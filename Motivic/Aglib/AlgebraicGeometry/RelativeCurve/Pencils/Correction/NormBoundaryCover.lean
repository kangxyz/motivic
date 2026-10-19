/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.OriginalNormBoundaryRange
/-! # The actual retained complement is covered by the full norm boundary

This is only a support calculation for the principal-action consumer. Equality
of boundary sections is supplied separately by the full scheme normalization.

Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.NormBoundaryCover`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`Pencils.NativeCorrectionNormAction`.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Hom

/-- The original puncture complement and projective boundary cover the entire
complement of the actual retained product. No coefficient open is changed. -/
theorem correctionNorm_retained_complement_subset_fullBoundary
    {S P X A D Z U : Scheme.{u}} (π : P ⟶ S) (b : A ⟶ S)
    (j : X ⟶ P) (v : U ⟶ X) (d : D ⟶ P) (z : Z ⟶ X)
    (hinfty : (Set.range j)ᶜ ⊆ Set.range d)
    (hpuncture : (Set.range v)ᶜ ⊆ Set.range z) :
    (Set.range (RelativeCurvePencil.retainedProductInclusion b π (v ≫ j)))ᶜ ⊆
      Set.range (normFullBoundaryMap π b d (z ≫ j)) := by
  rw [range_normFullBoundaryMap,
    Scheme.range_snd_eq_preimage_of_isPullback _ _ _ _
      (RelativeCurvePencil.retainedProductInclusion_isPullback b π (v ≫ j))]
  intro x hx
  change (pullback.snd b π) x ∈ Set.range d ∪ Set.range (z ≫ j)
  by_cases hj : (pullback.snd b π) x ∈ Set.range j
  · obtain ⟨y, hy⟩ := hj
    have hv : y ∉ Set.range v := by
      rintro ⟨u, rfl⟩
      exact hx ⟨u, by simpa only [Scheme.Hom.comp_apply] using hy⟩
    obtain ⟨w, hw⟩ := hpuncture hv
    exact Or.inr ⟨w, by simpa only [Scheme.Hom.comp_apply, hw] using hy⟩
  · exact Or.inl (hinfty hj)

end AlgebraicGeometry.Scheme.Hom
