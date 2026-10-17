/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.RetainedPrescribedLift

/-! # The original full étale closed square on the retained affine target -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurve
variable {X N Z S Y : Scheme.{u}} (i : X ⟶ N) [IsOpenImmersion i]
  (q : N ⟶ S) (f : X ⟶ S) (hi : i ≫ q = f)
  (T : S.Opens) (V : N.Opens) (hV : (V : Set N) ⊆ Set.range i)
  (z : Z ⟶ X) (hz : ∀ x : Z, (z ≫ f) x ∈ T → i (z x) ∈ V)
  (p : Y ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z)

/-- The lifted original closed scheme in the literal pullback of the original étale map. -/
def retainedEtaleClosedLift : ((z ≫ f) ⁻¹ᵁ T).toScheme ⟶
    pullback p (retainedBaseToOriginal i q T V hV) :=
  pullback.lift (((z ≫ f) ⁻¹ᵁ T).ι ≫ s)
    (prescribedBaseToRetained i q f hi T V hV z hz)
    (by rw [Category.assoc, hs, prescribedBaseToRetained_original])

@[reassoc (attr := simp)]
theorem retainedEtaleClosedLift_fst :
    retainedEtaleClosedLift i q f hi T V hV z hz p s hs ≫ pullback.fst _ _ =
      ((z ≫ f) ⁻¹ᵁ T).ι ≫ s := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem retainedEtaleClosedLift_snd :
    retainedEtaleClosedLift i q f hi T V hV z hz p s hs ≫ pullback.snd _ _ =
      prescribedBaseToRetained i q f hi T V hV z hz := pullback.lift_snd _ _ _

/-- The entire original base-restricted closed scheme is retained with identity bottom map. -/
theorem retainedEtaleClosedLift_isPullback (H : IsPullback s (𝟙 Z) p z) :
    IsPullback (retainedEtaleClosedLift i q f hi T V hV z hz p s hs) (𝟙 _)
      (pullback.snd p (retainedBaseToOriginal i q T V hV))
      (prescribedBaseToRetained i q f hi T V hV z hz) := by
  have Hbig := (IsPullback.of_id_snd (f := ((z ≫ f) ⁻¹ᵁ T).ι)).paste_horiz H
  rw [← prescribedBaseToRetained_original i q f hi T V hV z hz] at Hbig
  apply IsPullback.of_right (h₁₂ := pullback.fst p (retainedBaseToOriginal i q T V hV))
    ?_ ?_ (IsPullback.of_hasPullback _ _)
  · simpa only [retainedEtaleClosedLift_fst] using Hbig
  · simp only [retainedEtaleClosedLift_snd, Category.id_comp]

/-- The full closed lift is derived from the actual Cartesian square and prescribed finiteness. -/
theorem retainedEtaleClosedLift_closed [IsClosedImmersion z] [IsSeparated q]
    [IsFinite (z ≫ f)] (H : IsPullback s (𝟙 Z) p z) :
    IsClosedImmersion (retainedEtaleClosedLift i q f hi T V hV z hz p s hs) := by
  have := prescribedBaseToRetained_closed i q f hi T V hV z hz
  exact MorphismProperty.of_isPullback
    (retainedEtaleClosedLift_isPullback i q f hi T V hV z hz p s hs H).flip
    (inferInstance : IsClosedImmersion (prescribedBaseToRetained i q f hi T V hV z hz))

end AlgebraicGeometry.Scheme.RelativeCurve
