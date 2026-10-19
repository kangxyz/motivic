/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
# Pullbacks of étale morphisms in the smooth site

The smooth site need not have arbitrary pullbacks. This file constructs the
actual scheme pullback when one of its two arrows is étale and proves that
forgetting to schemes preserves precisely these pullbacks. No restriction on
the base or on the connected components of the objects is needed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}} {X Y Z : SmoothSite S}

instance isSeparated_hom (f : X ⟶ Y) : IsSeparated f.left := by
  have : IsSeparated (f.left ≫ Y.hom) := by rw [MorphismProperty.Over.w]; infer_instance
  exact IsSeparated.of_comp f.left Y.hom

instance quasiCompact_hom (f : X ⟶ Y) : QuasiCompact f.left := by
  have : QuasiCompact (f.left ≫ Y.hom) := by rw [MorphismProperty.Over.w]; infer_instance
  exact QuasiCompact.of_comp f.left Y.hom

/-- The actual scheme pullback of an étale arrow and an arbitrary smooth-site arrow. -/
def etalePullback (f : X ⟶ Z) (g : Y ⟶ Z) [Etale f.left] : SmoothSite S :=
  mk (pullback.snd f.left g.left ≫ Y.hom)

/-- First projection from the actual étale pullback. -/
def etalePullbackFst (f : X ⟶ Z) (g : Y ⟶ Z) [Etale f.left] :
    etalePullback f g ⟶ X :=
  homMk (pullback.fst f.left g.left) (by
    change pullback.fst f.left g.left ≫ X.hom = pullback.snd f.left g.left ≫ Y.hom
    rw [← MorphismProperty.Over.w f, ← MorphismProperty.Over.w g,
      ← Category.assoc, pullback.condition, Category.assoc])

/-- Second projection from the actual étale pullback. -/
def etalePullbackSnd (f : X ⟶ Z) (g : Y ⟶ Z) [Etale f.left] :
    etalePullback f g ⟶ Y :=
  homMk (pullback.snd f.left g.left) rfl

@[simp] theorem etalePullbackFst_left (f : X ⟶ Z) (g : Y ⟶ Z) [Etale f.left] :
    (etalePullbackFst f g).left = pullback.fst f.left g.left := rfl

@[simp] theorem etalePullbackSnd_left (f : X ⟶ Z) (g : Y ⟶ Z) [Etale f.left] :
    (etalePullbackSnd f g).left = pullback.snd f.left g.left := rfl

/-- The concrete étale pullback cone in the smooth category. -/
def etalePullbackCone (f : X ⟶ Z) (g : Y ⟶ Z) [Etale f.left] : PullbackCone f g :=
  PullbackCone.mk (etalePullbackFst f g) (etalePullbackSnd f g) (by
    apply MorphismProperty.Over.Hom.ext
    exact pullback.condition)

/-- The scheme universal property restricts to the full category of smooth objects. -/
def etalePullbackConeIsLimit (f : X ⟶ Z) (g : Y ⟶ Z) [Etale f.left] :
    IsLimit (etalePullbackCone f g) := by
  refine PullbackCone.IsLimit.mk _ (fun c ↦ homMk
    (pullback.lift c.fst.left c.snd.left (by
      exact congrArg (fun h ↦ h.left) c.condition)) ?_) ?_ ?_ ?_
  · change pullback.lift _ _ _ ≫ (pullback.snd f.left g.left ≫ Y.hom) = _
    rw [← Category.assoc, pullback.lift_snd, MorphismProperty.Over.w]
  · intro c
    apply MorphismProperty.Over.Hom.ext
    exact pullback.lift_fst _ _ _
  · intro c
    apply MorphismProperty.Over.Hom.ext
    exact pullback.lift_snd _ _ _
  · intro c m h₁ h₂
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext
    · exact (congrArg (fun h ↦ h.left) h₁).trans
        (pullback.lift_fst (f := f.left) (g := g.left) c.fst.left c.snd.left _).symm
    · exact (congrArg (fun h ↦ h.left) h₂).trans
        (pullback.lift_snd (f := f.left) (g := g.left) c.fst.left c.snd.left _).symm

instance hasPullback_of_etale (f : X ⟶ Z) (g : Y ⟶ Z) [Etale f.left] :
    HasPullback f g :=
  ⟨⟨etalePullbackCone f g, etalePullbackConeIsLimit f g⟩⟩

instance forgetScheme_preservesPullback_of_etale (f : X ⟶ Z) (g : Y ⟶ Z)
    [Etale f.left] : PreservesLimit (cospan f g) (forgetScheme S) := by
  apply preservesLimit_of_preserves_limit_cone (etalePullbackConeIsLimit f g)
  apply (PullbackCone.isLimitMapConeEquiv (etalePullbackCone f g) (forgetScheme S)).symm.toFun
  exact pullbackIsPullback f.left g.left

instance forget_preservesPullback_of_etale (f : X ⟶ Z) (g : Y ⟶ Z)
    [Etale f.left] : PreservesLimit (cospan f g) (forget S) :=
  preservesLimit_of_reflects_of_preserves (forget S) (Over.forget S)

end AlgebraicGeometry.Scheme.SmoothSite
