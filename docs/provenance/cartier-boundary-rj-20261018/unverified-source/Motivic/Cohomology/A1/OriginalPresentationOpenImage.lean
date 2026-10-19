/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.OriginalEtalePresentation
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.BoundaryBaseCover

/-! # The retained presentation target is an actual original affine open

The two presentation restrictions are not treated as a replacement coefficient
scheme. Their composite with the original open immersion has a literal affine
open image, with a canonical isomorphism commuting with the original inclusion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation

variable {k : Type u} [Field k] {X Y A Z : Scheme.{u}}
  {b : X ⟶ Spec (.of k)} {p : Y ⟶ X} {a : A ⟶ X}
  {z : Z ⟶ X} {s : Z ⟶ Y} {x : X}
  (e : OriginalEtalePresentation k b p a z s x)

local instance openImageRefinement : IsOpenImmersion e.refinement := e.refinement_open

variable (U : e.target.Opens) (V : (Spec e.base).Opens)

/-- The retained affine target maps to the unchanged original scheme. -/
abbrev retainedToOriginal :=
  (boundaryBaseSourceOpen
    (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) U V).ι ≫ e.refinement

/-- The actual original open occupied by the base-and-source restriction. -/
abbrev retainedOriginalOpen : X.Opens := (retainedToOriginal e U V).opensRange

/-- Affineness is transported through the canonical open-image isomorphism. -/
theorem retainedOriginalOpen_affine
    [IsAffine (boundaryBaseSourceOpen
      (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) U V).toScheme] :
    IsAffineOpen (retainedOriginalOpen e U V) :=
  isAffineOpen_opensRange (retainedToOriginal e U V)

/-- The selected original point survives both genuine restrictions. In the
zero-section application this is precisely the original zero point, not a rational lift. -/
theorem point_mem_retainedOriginalOpen
    (hU : e.point ∈ U)
    (hV : (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) e.point ∈ V) :
    x ∈ retainedOriginalOpen e U V := by
  refine ⟨⟨e.point, ⟨hU, hV⟩⟩, ?_⟩
  exact e.point_eq

/-- The restriction is canonically the literal affine open in the original target. -/
def retainedOriginalOpenIso :
    (boundaryBaseSourceOpen
      (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) U V).toScheme ≅
        (retainedOriginalOpen e U V).toScheme :=
  (retainedToOriginal e U V).isoOpensRange

@[reassoc (attr := simp)] theorem retainedOriginalOpenIso_hom_ι :
    (retainedOriginalOpenIso e U V).hom ≫ (retainedOriginalOpen e U V).ι =
      retainedToOriginal e U V :=
  Scheme.Hom.isoOpensRange_hom_ι _

@[reassoc (attr := simp)] theorem retainedOriginalOpenIso_inv_original :
    (retainedOriginalOpenIso e U V).inv ≫ retainedToOriginal e U V =
      (retainedOriginalOpen e U V).ι :=
  Scheme.Hom.isoOpensRange_inv_comp _

/-- Restricting either original arrow through the presentation gives its genuine
pullback to the literal original open. This applies uniformly to the étale arrow
and the puncture inclusion. -/
theorem retainedOriginalPullback_isPullback {Q : Scheme.{u}} (t : Q ⟶ X) :
    IsPullback
      (boundaryBaseCoverMap
        (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _)
        (pullback.snd t e.refinement) U V ≫ (retainedOriginalOpenIso e U V).hom)
      ((boundaryBaseCoverOpen
        (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _)
        (pullback.snd t e.refinement) U V).ι ≫ pullback.fst t e.refinement)
      (retainedOriginalOpen e U V).ι t := by
  have H := (isPullback_morphismRestrict (pullback.snd t e.refinement)
    (boundaryBaseSourceOpen
      (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) U V)).paste_vert
        (IsPullback.of_hasPullback t e.refinement).flip
  apply H.of_iso (Iso.refl _) (retainedOriginalOpenIso e U V) (Iso.refl _) (Iso.refl _)
  · simp
  · simp
  · simp
  · simp

/-- Canonical identification with the original-arrow pullback, rather than an
unspecified isomorphic neighborhood. -/
def retainedOriginalPullbackIso {Q : Scheme.{u}} (t : Q ⟶ X) :
    (boundaryBaseCoverOpen
      (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _)
      (pullback.snd t e.refinement) U V).toScheme ≅
        pullback (retainedOriginalOpen e U V).ι t :=
  (retainedOriginalPullback_isPullback e U V t).isoPullback

@[reassoc (attr := simp)] theorem retainedOriginalPullbackIso_hom_fst
    {Q : Scheme.{u}} (t : Q ⟶ X) :
    (retainedOriginalPullbackIso e U V t).hom ≫
        pullback.fst (retainedOriginalOpen e U V).ι t =
      boundaryBaseCoverMap
        (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _)
        (pullback.snd t e.refinement) U V ≫ (retainedOriginalOpenIso e U V).hom :=
  (retainedOriginalPullback_isPullback e U V t).isoPullback_hom_fst

@[reassoc (attr := simp)] theorem retainedOriginalPullbackIso_hom_snd
    {Q : Scheme.{u}} (t : Q ⟶ X) :
    (retainedOriginalPullbackIso e U V t).hom ≫
        pullback.snd (retainedOriginalOpen e U V).ι t =
      (boundaryBaseCoverOpen
        (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _)
        (pullback.snd t e.refinement) U V).ι ≫ pullback.fst t e.refinement :=
  (retainedOriginalPullback_isPullback e U V t).isoPullback_hom_snd

/-- In particular, the retained original puncture is exactly the intersection
with the original puncture open, before applying any presheaf. -/
def retainedOriginalPunctureIso (D : X.Opens) :
    (boundaryBaseCoverOpen
      (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _)
      (pullback.snd D.ι e.refinement) U V).toScheme ≅
        (retainedOriginalOpen e U V ⊓ D).toScheme :=
  retainedOriginalPullbackIso e U V D.ι ≪≫
    (isPullback_opens_inf (retainedOriginalOpen e U V) D).isoPullback.symm

@[reassoc (attr := simp)] theorem retainedOriginalPunctureIso_hom_left (D : X.Opens) :
    (retainedOriginalPunctureIso e U V D).hom ≫ X.homOfLE inf_le_left =
      boundaryBaseCoverMap
        (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _)
        (pullback.snd D.ι e.refinement) U V ≫ (retainedOriginalOpenIso e U V).hom := by
  simp [retainedOriginalPunctureIso, Category.assoc]

/-- The puncture identification commutes with the unchanged original inclusion. -/
@[reassoc (attr := simp)] theorem retainedOriginalPunctureIso_hom_ι (D : X.Opens) :
    (retainedOriginalPunctureIso e U V D).hom ≫ (retainedOriginalOpen e U V ⊓ D).ι =
      (boundaryBaseCoverOpen
        (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _)
        (pullback.snd D.ι e.refinement) U V).ι ≫ pullback.fst D.ι e.refinement ≫ D.ι := by
  calc
    _ = (retainedOriginalPunctureIso e U V D).hom ≫
        X.homOfLE inf_le_left ≫ (retainedOriginalOpen e U V).ι := by simp
    _ = (boundaryBaseCoverMap
        (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _)
        (pullback.snd D.ι e.refinement) U V ≫
          (retainedOriginalOpenIso e U V).hom) ≫ (retainedOriginalOpen e U V).ι := by
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (fun f => f ≫ (retainedOriginalOpen e U V).ι)
          (retainedOriginalPunctureIso_hom_left e U V D))
    _ = _ := (retainedOriginalPullback_isPullback e U V D.ι).w.trans (Category.assoc _ _ _)

end AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation
