/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Compactification.Retained.NormalRetainedBaseRestriction
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.Boundary.TargetChartBoundary

/-! # The unchanged original étale map on the actual retained affine target -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurve
variable {X N S : Scheme.{u}} (i : X ⟶ N) [IsOpenImmersion i]
  (q : N ⟶ S) (T : S.Opens) (V : N.Opens) (hV : (V : Set N) ⊆ Set.range i)

/-- The retained target maps to the original target through its original open embedding. -/
def retainedBaseToOriginal : (retainedBaseOpen q T V).toScheme ⟶ X :=
  (retainedBaseOpen q T V).ι ≫ IsOpenImmersion.lift i V.ι
    (by simpa only [Scheme.Opens.range_ι] using hV)

@[reassoc (attr := simp)]
theorem retainedBaseToOriginal_comp :
    retainedBaseToOriginal i q T V hV ≫ i =
      (retainedBaseOpen q T V).ι ≫ V.ι := by
  simp [retainedBaseToOriginal]

instance : IsOpenImmersion (retainedBaseToOriginal i q T V hV) := by
  have : IsOpenImmersion (retainedBaseToOriginal i q T V hV ≫ i) := by
    rw [retainedBaseToOriginal_comp]
    infer_instance
  exact IsOpenImmersion.of_comp _ i

/-- The original point, not an arbitrary point above it, is retained. -/
theorem retainedBaseToOriginal_point (x : X) (hxV : i x ∈ V) (hxT : q (i x) ∈ T) :
    retainedBaseToOriginal i q T V hV ⟨⟨i x, hxV⟩, hxT⟩ = x := by
  apply i.isOpenEmbedding.injective
  exact congrArg (fun f => f ⟨⟨i x, hxV⟩, hxT⟩)
    (retainedBaseToOriginal_comp i q T V hV)

end AlgebraicGeometry.Scheme.RelativeCurve

namespace AlgebraicGeometry.Scheme
/-- Finiteness over the original good chart survives the actual Cartesian target change. -/
theorem finite_pullback_on_original_chart {X Y X' : Scheme.{u}}
    (p : Y ⟶ X) (a : X' ⟶ X) (U : X.Opens) [IsFinite (p ∣_ U)] :
    IsFinite ((pullback.snd p a) ∣_ a ⁻¹ᵁ U) := by
  let H := IsPullback.of_hasPullback p a
  have hUY : (pullback.snd p a) ⁻¹ᵁ (a ⁻¹ᵁ U) =
      (pullback.fst p a) ⁻¹ᵁ (p ⁻¹ᵁ U) ⊓
        (pullback.snd p a) ⁻¹ᵁ (a ⁻¹ᵁ U) := by
    simp only [← Scheme.Hom.comp_preimage, H.w, inf_idem]
  have H' := Scheme.Hom.isPullback_resLE H (US := U) (UT := a ⁻¹ᵁ U)
    (UX := p ⁻¹ᵁ U) le_rfl le_rfl hUY
  simp only [Scheme.Hom.resLE_eq_morphismRestrict] at H'
  exact MorphismProperty.of_isPullback H' (inferInstance : IsFinite (p ∣_ U))

end AlgebraicGeometry.Scheme
