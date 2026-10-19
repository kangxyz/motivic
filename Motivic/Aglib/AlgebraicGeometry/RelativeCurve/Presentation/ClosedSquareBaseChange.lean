/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Presentation.OriginalEtaleMap

/-! # The entire original closed square under the actual retained-target base change -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurve
variable {X Y Z X' : Scheme.{u}} (p : Y ⟶ X) (z : Z ⟶ X) (s : Z ⟶ Y)
  (hs : s ≫ p = z) (a : X' ⟶ X)

/-- The original full closed scheme and its original lift are base changed together. -/
def originalClosedBaseChangeLift : pullback z a ⟶ pullback p a :=
  pullback.lift (pullback.fst z a ≫ s) (pullback.snd z a)
    (by rw [Category.assoc, hs, pullback.condition])

@[reassoc (attr := simp)]
theorem originalClosedBaseChangeLift_fst :
    originalClosedBaseChangeLift p z s hs a ≫ pullback.fst p a =
      pullback.fst z a ≫ s := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem originalClosedBaseChangeLift_snd :
    originalClosedBaseChangeLift p z s hs a ≫ pullback.snd p a =
      pullback.snd z a := pullback.lift_snd _ _ _

/-- The literal identity-on-closed-scheme Cartesian square survives unchanged. -/
theorem originalClosedBaseChangeLift_isPullback (H : IsPullback s (𝟙 Z) p z) :
    IsPullback (originalClosedBaseChangeLift p z s hs a) (𝟙 _)
      (pullback.snd p a) (pullback.snd z a) := by
  have Hbig := (IsPullback.of_id_snd (f := pullback.fst z a)).paste_horiz H
  rw [pullback.condition] at Hbig
  apply IsPullback.of_right (h₁₂ := pullback.fst p a) ?_ ?_
    (IsPullback.of_hasPullback p a)
  · simpa only [originalClosedBaseChangeLift_fst] using Hbig
  · simp only [originalClosedBaseChangeLift_snd, Category.id_comp]

/-- This is the full closed immersion, not a reduced closed-fiber replacement. -/
theorem originalClosedBaseChangeLift_closed [IsClosedImmersion z]
    (H : IsPullback s (𝟙 Z) p z) :
    IsClosedImmersion (originalClosedBaseChangeLift p z s hs a) :=
  MorphismProperty.of_isPullback (originalClosedBaseChangeLift_isPullback p z s hs a H).flip
    (inferInstance : IsClosedImmersion (pullback.snd z a))

end AlgebraicGeometry.Scheme.RelativeCurve
