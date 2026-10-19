/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.PencilSites
/-! # The actual smaller parameter inside the unchanged base-restricted target

This is the identity-cover specialization without replacing either target by the
parameter open. The whole original closed boundary is retained scheme-theoretically.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ProjectiveSpace
open Scheme.Hom Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Moving
variable {S X C Z D : Scheme.{u}} (q : X ⟶ S) (π : C ⟶ S)
  (x : X ⟶ C) (hx : x ≫ π = q) (U : X.Opens) (W : S.Opens)

def refinedParameterInclusion : (boundaryBaseSourceOpen q U W).toScheme ⟶
    boundaryBaseCompactification π W :=
  pullback.lift (boundaryBaseSourceProjection q U W)
    ((boundaryBaseSourceOpen q U W).ι ≫ x) (by
      rw [Category.assoc, hx, boundaryBaseSourceProjection_ι])

@[reassoc (attr := simp)] theorem refinedParameterInclusion_fst :
    refinedParameterInclusion q π x hx U W ≫ pullback.fst W.ι π =
      boundaryBaseSourceProjection q U W := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem refinedParameterInclusion_snd :
    refinedParameterInclusion q π x hx U W ≫ pullback.snd W.ι π =
      (boundaryBaseSourceOpen q U W).ι ≫ x := pullback.lift_snd _ _ _

instance [IsOpenImmersion x] : IsOpenImmersion (refinedParameterInclusion q π x hx U W) := by
  have : IsOpenImmersion
      (refinedParameterInclusion q π x hx U W ≫ pullback.snd W.ι π) := by
    rw [refinedParameterInclusion_snd]
    infer_instance
  exact IsOpenImmersion.of_comp _ (pullback.snd W.ι π)

/-- The parameter lies in the base restriction of the entire original target. -/
def refinedParameterToTarget : (boundaryBaseSourceOpen q U W).toScheme ⟶
    ((x ≫ π) ⁻¹ᵁ W).toScheme :=
  X.homOfLE (by rw [hx]; exact inf_le_right)

@[reassoc (attr := simp)] theorem refinedParameterToTarget_ι :
    refinedParameterToTarget q π x hx U W ≫ ((x ≫ π) ⁻¹ᵁ W).ι =
      (boundaryBaseSourceOpen q U W).ι := by
  simp [refinedParameterToTarget]

theorem refinedParameterToTarget_inclusion :
    refinedParameterToTarget q π x hx U W ≫ boundaryBaseRetainedTarget π W x =
      refinedParameterInclusion q π x hx U W := by
  apply (cancel_mono (pullback.snd W.ι π)).mp
  simp only [boundaryBaseRetainedTarget, Category.assoc, boundaryBaseWholeMap_snd,
    refinedParameterInclusion_snd]
  exact refinedParameterToTarget_ι_assoc q π x hx U W x

variable (z : Z ⟶ X) (h : ∀ b : Z, (z ≫ q) b ∈ W → z b ∈ U)

/-- This equality retains the original closed scheme and its structural map. -/
@[reassoc (attr := simp)] theorem refinedZero_inclusion_snd :
    (boundaryBaseLift q z U W h ≫ refinedParameterInclusion q π x hx U W) ≫
      pullback.snd W.ι π = (boundaryBaseClosedOpen q z W).ι ≫ z ≫ x := by
  simp only [Category.assoc, refinedParameterInclusion_snd, boundaryBaseLift_ι_assoc]

/-- The canonical identity-cover specialization has exactly this same full zero. -/
theorem refinedZero_eq_cover :
    boundaryBaseLift q z U W h ≫ refinedParameterInclusion q π x hx U W =
      boundaryBaseCoverLift q (𝟙 X) z z (by simp) U W h ≫
        boundaryBaseCoverInclusion q (𝟙 X) π x (by simpa using hx) U W := by
  apply (cancel_mono (pullback.snd W.ι π)).mp
  simp only [Category.assoc, boundaryBaseCoverInclusion_snd,
    boundaryBaseCoverLift_ι_assoc, refinedParameterInclusion_snd, boundaryBaseLift_ι_assoc]

theorem refinedZero_isPullback :
    IsPullback (boundaryBaseClosedOpen q z W).ι
      (boundaryBaseLift q z U W h ≫ refinedParameterInclusion q π x hx U W)
      (z ≫ x) (pullback.snd W.ι π) := by
  rw [refinedZero_eq_cover]
  exact boundaryBaseSourceZero_isPullback q (𝟙 X) z z (by simp) π x
    (by simpa using hx) U W h

instance [IsClosedImmersion (z ≫ x)] :
    IsClosedImmersion
      (boundaryBaseLift q z U W h ≫ refinedParameterInclusion q π x hx U W) :=
  MorphismProperty.of_isPullback
    (refinedZero_isPullback q π x hx U W z h) inferInstance

section Projective
variable (R : Type u) [CommRing R] (ι : Type u) {X C : Scheme.{u}}
  (f : C ⟶ ProjectiveSpace R ι) (q : X ⟶ Spec (.of R)) (x : X ⟶ C)
  (hx : x ≫ (f ≫ toSpec R ι) = q) (U : X.Opens)
  (W : (Spec (.of R)).Opens) [IsAffine W.toScheme]

@[reassoc] theorem refinedParameterInclusion_projective :
    refinedParameterInclusion q (f ≫ toSpec R ι) x hx U W ≫
      (boundaryBaseProjectiveMap R ι f W ≫ toSpec Γ(W.toScheme, ⊤) ι) =
        boundaryBaseSpecProjection q U W := by
  rw [boundaryBaseProjectiveMap_toSpec, ← Category.assoc, refinedParameterInclusion_fst]
  rfl

instance [SmoothOfRelativeDimension 1 q] :
    SmoothOfRelativeDimension 1
      (refinedParameterInclusion q (f ≫ toSpec R ι) x hx U W ≫
        (boundaryBaseProjectiveMap R ι f W ≫ toSpec Γ(W.toScheme, ⊤) ι)) := by
  rw [refinedParameterInclusion_projective]
  infer_instance
end Projective
end AlgebraicGeometry.Scheme.Moving
