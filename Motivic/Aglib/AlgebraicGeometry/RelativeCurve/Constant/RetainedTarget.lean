/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Constant.EtaleCurve
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.AffineLine.RetainedTarget

/-! # Constant curves with the original overlap as their actual target -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
variable (k : Type u) [Field k] {Y S : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]
  (U : (Spec (.of (Polynomial k))).Opens) (q : S ⟶ Spec (.of k))

/-- The structure map of the retained open through the compactification. -/
abbrev retainedProjection := retainedInclusion k p U ≫ projection k p
/-- The retained target pulled back along the base structure map `q`. -/
abbrev constantRetainedTarget := pullback q (retainedProjection k p U)

/-- This actual open has a global map to the original overlap, not merely to Y. -/
def constantRetainedInclusion : constantRetainedTarget k p U q ⟶
    constantCompactification k p q :=
  (IsPullback.of_hasPullback q (projection k p)).flip.lift
    (pullback.snd _ _ ≫ retainedInclusion k p U) (pullback.fst _ _) (by
      rw [Category.assoc, ← pullback.condition])

omit [IsSeparated p] in
@[reassoc (attr := simp)]
theorem constantRetainedInclusion_fst : constantRetainedInclusion k p U q ≫
    pullback.fst _ _ = pullback.fst _ _ :=
  (IsPullback.of_hasPullback q (projection k p)).flip.lift_snd _ _ _

omit [IsSeparated p] in
@[reassoc (attr := simp)]
theorem constantRetainedInclusion_snd : constantRetainedInclusion k p U q ≫
    pullback.snd _ _ = pullback.snd _ _ ≫ retainedInclusion k p U :=
  (IsPullback.of_hasPullback q (projection k p)).flip.lift_fst _ _ _

omit [IsSeparated p] in
theorem constantRetainedInclusion_isPullback :
    IsPullback (pullback.snd _ _) (constantRetainedInclusion k p U q)
      (retainedInclusion k p U) (pullback.snd q (projection k p)) :=
  (IsPullback.of_hasPullback q (retainedProjection k p U)).flip.of_bot'
    (IsPullback.of_hasPullback q (projection k p)).flip

instance : IsOpenImmersion (constantRetainedInclusion k p U q) :=
  MorphismProperty.of_isPullback (constantRetainedInclusion_isPullback k p U q) inferInstance

omit [IsSeparated p] in
/-- Smoothness is derived on the retained overlap, not on the compactification. -/
theorem constantRetainedTarget_smooth :
    SmoothOfRelativeDimension 1 (pullback.fst q (retainedProjection k p U)) := by
  have := polynomialProjection_smooth_one k
  have : SmoothOfRelativeDimension 1 (retainedProjection k p U) := by
    change SmoothOfRelativeDimension 1
      ((pullback.snd U.ι p ≫ inclusion k p) ≫ projection k p)
    rw [Category.assoc, inclusion_projection]
    exact inferInstanceAs (SmoothOfRelativeDimension (0 + (0 + 1)) _)
  exact MorphismProperty.pullback_fst _ _ inferInstance

/-- The original common target remains quasi-affine over an affine source. -/
theorem constantRetainedTarget_quasiAffine [IsAffine S] :
    (constantRetainedTarget k p U q).IsQuasiAffine := by
  let pB := pullback.snd U.ι p ≫ p
  have : Etale pB := inferInstance
  have : QuasiCompact pB := inferInstance
  have : IsSeparated pB := inferInstance
  have he : retainedProjection k p U = curveProjection k pB := by
    simp only [retainedProjection, retainedInclusion, Category.assoc, inclusion_projection,
      curveProjection, pB]
  change (pullback q (retainedProjection k p U)).IsQuasiAffine
  rw [he]
  exact constantCurve_quasiAffine k pB q
omit [IsSeparated p] in
/-- The relative retained open has exactly the inverse image of the original target support. -/
theorem range_constantRetainedInclusion : Set.range (constantRetainedInclusion k p U q) =
    (pullback.snd q (projection k p)) ⁻¹' Set.range (retainedInclusion k p U) := by
  let H := constantRetainedInclusion_isPullback k p U q
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨(pullback.snd q (retainedProjection k p U)) v,
      congrArg (fun m => m v) H.w⟩
  · rintro ⟨v, hv⟩
    obtain ⟨w, _, hw⟩ := Scheme.exists_preimage_of_isPullback H v x hv
    exact ⟨w, hw⟩

/-- Avoiding the full two-part boundary gives precisely the open with original overlap target. -/
theorem range_constantRetainedInclusion_complement {Z : Scheme.{u}}
    (z : Z ⟶ Spec (.of (Polynomial k))) (s : Z ⟶ Y)
    (H : IsPullback s (𝟙 _) p z)
    (hz : Set.range z = (U : Set (Spec (.of (Polynomial k))))ᶜ) :
    Set.range (constantRetainedInclusion k p U q) =
      ((pullback.snd q (projection k p)) ⁻¹'
        (Set.range (infinityInclusion k p) ∪ Set.range (s ≫ inclusion k p)))ᶜ := by
  rw [range_constantRetainedInclusion, range_retainedInclusion k p U z s H hz,
    Set.preimage_compl]
end AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
