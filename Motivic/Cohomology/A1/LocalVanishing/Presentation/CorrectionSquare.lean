/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.LocalVanishing.Presentation.OverlapLifting
public import Motivic.Cohomology.A1.LocalVanishing.Presentation.OpenImage

/-! # The actual retained correction square and its original projections -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.RelativeCurvePencil
open AlgebraicGeometry.Scheme.EtaleCompactification

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation

variable {k : Type u} [Field k] {X Y A : SmoothSite (Spec (.of k))}
  [IsAffine X.left] [IsAffine Y.left] [IsAffine A.left]
  (p : Y ⟶ X) [Etale p.left] (a : A ⟶ X) [IsOpenImmersion a.left]
  {Z : Scheme.{u}} (z : Z ⟶ X.left) (s : Z ⟶ Y.left) (x : X.left)
  (e : OriginalEtalePresentation k X.hom p.left a.left z s x)

local instance correctionSquareTarget : IsAffine e.target := e.target_affine
local instance correctionSquareRefinement : IsOpenImmersion e.refinement := e.refinement_open
local instance correctionSquareField : Smooth e.toField := e.base_smooth
local instance correctionSquareIntegral : IsIntegral e.compact := e.compact_integral
local instance correctionSquareNoetherian : IsLocallyNoetherian e.compact := e.compact_noetherian
local instance correctionSquareNormal (c : e.compact) :
    IsIntegrallyClosed (e.compact.presheaf.stalk c) :=
  e.compact_normal c
local instance correctionSquareFinite : IsFinite e.projectiveMap := e.projective_finite
local instance correctionSquareInclusion : IsOpenImmersion e.inclusion := e.inclusion_open
local instance correctionSquareSmooth : SmoothOfRelativeDimension 1
    (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) := e.target_smooth

variable (U : e.target.Opens) (V : (Spec e.base).Opens)
  [IsAffine V.toScheme]
  [IsAffine (boundaryBaseSourceOpen
    (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) U V).toScheme]

/-- The first correction is its literal base-restricted cartesian square. -/
abbrev retainedCorrectionSquare :=
  boundaryBasePencilSquare k e.base (ULift.{u} (Fin 2)) e.toField
    (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _)
    (pullback.snd p.left e.refinement) (pullback.snd a.left e.refinement)
    (fixedTargetSourceProjectiveMap e.base (ULift.{u} (Fin 2)) e.target e.compact
      (pullback.snd p.left e.refinement) e.inclusion e.projectiveMap)
    (EtaleCompactification.inclusion e.compact (pullback.snd p.left e.refinement ≫ e.inclusion))
    (fixedTargetSource_over e.base (ULift.{u} (Fin 2)) e.target e.compact
      (pullback.snd p.left e.refinement) e.inclusion e.projectiveMap
      (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) rfl) U V

/-- The first correction's ambient source maps to the unchanged original source. -/
def retainedEtaleToOriginal : (retainedCorrectionSquare p a z s x e U V).X₃ ⟶ Y :=
  boundaryBaseEtaleRestriction k e.base (ULift.{u} (Fin 2)) e.toField
    (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _)
    (pullback.snd p.left e.refinement) _ _ _ U V ≫ etaleToOriginal p a z s x e

/-- The actual first correction restricts the unchanged original overlap. -/
def retainedOverlapToOriginal :
    (retainedCorrectionSquare p a z s x e U V).X₁ ⟶ SmoothSite.etalePullback p a :=
  fixedTargetOverlapRestriction k e.base (ULift.{u} (Fin 2)) e.target e.compact e.toField
    (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _)
    (pullback.snd p.left e.refinement) (pullback.snd a.left e.refinement)
    e.inclusion e.projectiveMap rfl U V ≫ overlapToOriginal p a z s x e

/-- The retained first square is cartesian before applying any presheaf. -/
theorem retainedCorrectionSquare_isPullback :
    (retainedCorrectionSquare p a z s x e U V).IsPullback :=
  boundaryBasePencilSquare_isPullback _ _ _ _ _ _ _ _ _ _ _ _

/-- The first correction's structural map is genuinely etale. -/
instance retainedCorrectionSquare_etale :
    Etale (retainedCorrectionSquare p a z s x e U V).f₃₄.left := by
  change Etale (boundaryBaseCoverMap _ _ U V)
  infer_instance

/-- Its original-source projection is the original overlap projection. -/
@[reassoc] theorem retainedOverlapToOriginal_etale :
    retainedOverlapToOriginal p a z s x e U V ≫ SmoothSite.etalePullbackFst p a =
      (retainedCorrectionSquare p a z s x e U V).f₁₃ ≫
        retainedEtaleToOriginal p a z s x e U V := by
  rw [retainedOverlapToOriginal, Category.assoc, overlapToOriginal_etale]
  rw [← Category.assoc, boundaryBaseOverlapRestriction_etale, Category.assoc]
  rfl

/-- The retained first source is the actual pullback of the original source to
its retained ambient open; this controls the entire original zero marking. -/
theorem retainedEtale_original_isPullback :
    IsPullback (retainedCorrectionSquare p a z s x e U V).f₃₄.left
      (retainedEtaleToOriginal p a z s x e U V).left
      (retainedToOriginal e U V) p.left := by
  exact (isPullback_morphismRestrict (pullback.snd p.left e.refinement)
    (boundaryBaseSourceOpen
      (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) U V)).paste_vert
        (IsPullback.of_hasPullback p.left e.refinement).flip

end AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation
