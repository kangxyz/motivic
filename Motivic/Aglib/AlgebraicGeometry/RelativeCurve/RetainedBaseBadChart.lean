/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.RetainedOriginalEtaleMap
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.QuotientRetainedBadCover

/-! # The literal original finite chart and complete bad boundary after the same base shrink -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurve

/-- The computed finite good chart on the actual retained target has exactly the
required complete bad-boundary cover, including the original nonreduced quotient. -/
theorem retained_base_bad_chart_cover (B : Type u) [CommRing B] (I : Ideal B)
    {N S : Scheme.{u}} (i : Spec (.of B) ⟶ N) [IsOpenImmersion i]
    (q : N ⟶ S) (T : S.Opens) (V : N.Opens) (hV : (V : Set N) ⊆ Set.range i)
    (U : (Spec (.of B)).Opens)
    (hU : (U : Set (Spec (.of B))) = (PrimeSpectrum.zeroLocus (I : Set B))ᶜ) :
    (retainedBaseInclusion q T V ''ᵁ (retainedBaseToOriginal i q T V hV ⁻¹ᵁ U) :
      Set (q ⁻¹ᵁ T).toScheme)ᶜ ⊆
      Set.range (coprod.desc (retainedBoundaryInclusion V ∣_ q ⁻¹ᵁ T)
        ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ i) ∣_ q ⁻¹ᵁ T)) := by
  intro x hx
  have hbad : x.val ∈ ((V ⊓ i ''ᵁ U : N.Opens) : Set N)ᶜ := by
    rintro ⟨hxV, y, hy, he⟩
    let w : (retainedBaseOpen q T V).toScheme := ⟨⟨x.val, hxV⟩, x.property⟩
    have hw : retainedBaseToOriginal i q T V hV w = y := by
      apply i.isOpenEmbedding.injective
      have hf := congrArg (fun f => f w) (retainedBaseToOriginal_comp i q T V hV)
      exact hf.trans he.symm
    apply hx
    refine ⟨w, ?_, ?_⟩
    · change retainedBaseToOriginal i q T V hV w ∈ U
      rwa [hw]
    · exact retainedBase_point q T V x.val hxV x.property
  rcases quotient_retained_bad_cover B I i U hU V hV hbad with hleft | hright
  · obtain ⟨y, hy⟩ := hleft
    have hym : y ∈ retainedBoundaryInclusion V ⁻¹ᵁ q ⁻¹ᵁ T := by
      change q (retainedBoundaryInclusion V y) ∈ T
      rw [hy]
      exact x.property
    refine ⟨(coprod.inl : (retainedBoundaryInclusion V ⁻¹ᵁ q ⁻¹ᵁ T).toScheme ⟶
      _ ⨿ _) ⟨y, hym⟩, ?_⟩
    rw [← Scheme.Hom.comp_apply, coprod.inl_desc]
    apply Subtype.ext
    exact (morphismRestrict_base_coe _ _ _).trans hy
  · obtain ⟨y, hy⟩ := hright
    have hym : y ∈ (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ i) ⁻¹ᵁ q ⁻¹ᵁ T := by
      change q ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ i) y) ∈ T
      rw [hy]
      exact x.property
    refine ⟨(coprod.inr :
      ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ i) ⁻¹ᵁ q ⁻¹ᵁ T).toScheme ⟶
        _ ⨿ _) ⟨y, hym⟩, ?_⟩
    rw [← Scheme.Hom.comp_apply, coprod.inr_desc]
    apply Subtype.ext
    exact (morphismRestrict_base_coe _ _ _).trans hy

end AlgebraicGeometry.Scheme.RelativeCurve
