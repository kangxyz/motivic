/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.A1.OriginalEtalePresentationLifting
public import Motivic.Cohomology.A1.OriginalOverlapSectionLifting
public import Motivic.AlgebraicGeometry.SmoothSiteNisnevichPullbacks

/-! # Original smooth-site maps of the constructed target presentation -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open AlgebraicGeometry.Scheme.Hom
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation
variable {k : Type u} [Field k] {X Y A : SmoothSite (Spec (.of k))}
  [IsAffine X.left] [IsAffine Y.left] [IsAffine A.left]
  (p : Y ⟶ X) [Etale p.left] (a : A ⟶ X) [IsOpenImmersion a.left]
  {Z : Scheme.{u}} (z : Z ⟶ X.left) (s : Z ⟶ Y.left) (x : X.left)
  (e : OriginalEtalePresentation k X.hom p.left a.left z s x)
local instance : IsAffine e.target := e.target_affine
local instance : IsOpenImmersion e.refinement := e.refinement_open
local instance : Smooth e.toField := e.base_smooth
local instance : SmoothOfRelativeDimension 1
    (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) := e.target_smooth

/-- The presentation's field structure is exactly the original one. -/
def targetToOriginal :
    originalAmbientSite k e.base e.toField
      (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) ⟶ X :=
  SmoothSite.homMk e.refinement e.base_compatibility

/-- The refined étale source maps to the unchanged original étale source. -/
def etaleToOriginal :
    originalEtaleSite k e.base e.toField
      (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _)
      (pullback.snd p.left e.refinement) ⟶ Y :=
  SmoothSite.homMk (pullback.fst p.left e.refinement) (by
    change pullback.fst p.left e.refinement ≫ Y.hom =
      pullback.snd p.left e.refinement ≫ e.inclusion ≫ e.projectiveMap ≫
        ProjectiveSpace.toSpec e.base _ ≫ e.toField
    rw [← MorphismProperty.Over.w p, ← Category.assoc, pullback.condition,
      Category.assoc, e.base_compatibility])

/-- The refined puncture maps to the unchanged original puncture. -/
def punctureToOriginal :
    originalOpenSite k e.base e.toField
      (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _)
      (pullback.snd a.left e.refinement) ⟶ A :=
  SmoothSite.homMk (pullback.fst a.left e.refinement) (by
    change pullback.fst a.left e.refinement ≫ A.hom =
      pullback.snd a.left e.refinement ≫ e.inclusion ≫ e.projectiveMap ≫
        ProjectiveSpace.toSpec e.base _ ≫ e.toField
    rw [← MorphismProperty.Over.w a, ← Category.assoc, pullback.condition,
      Category.assoc, e.base_compatibility])

/-- The actual scheme map between original overlap and its target refinement. -/
def overlapToOriginalScheme :
    pullback (pullback.snd p.left e.refinement) (pullback.snd a.left e.refinement) ⟶
      pullback p.left a.left :=
  pullback.map _ _ _ _ (pullback.fst p.left e.refinement)
    (pullback.fst a.left e.refinement) e.refinement
    (pullback.condition (f := p.left) (g := e.refinement)).symm
    (pullback.condition (f := a.left) (g := e.refinement)).symm

/-- The original punctured-section coefficient object is preserved over the field. -/
def overlapToOriginal :
    originalOverlapSite k e.base e.toField
      (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _)
      (pullback.snd p.left e.refinement) (pullback.snd a.left e.refinement) ⟶
      SmoothSite.etalePullback p a :=
  SmoothSite.homMk (overlapToOriginalScheme p a z s x e) (by
    change overlapToOriginalScheme p a z s x e ≫
      (pullback.snd p.left a.left ≫ A.hom) =
      pullback.fst _ _ ≫ pullback.snd p.left e.refinement ≫ e.inclusion ≫
        e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _ ≫ e.toField
    simp only [overlapToOriginalScheme, pullback.map, pullback.lift_snd_assoc]
    simp only [Category.assoc, ← MorphismProperty.Over.w a]
    rw [pullback.condition_assoc, e.base_compatibility]
    exact (pullback.condition_assoc _).symm)


end AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation
