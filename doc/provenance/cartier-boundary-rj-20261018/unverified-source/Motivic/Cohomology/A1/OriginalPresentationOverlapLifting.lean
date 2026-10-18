/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.FixedTargetOriginalOverlapLifting
public import Motivic.Cohomology.A1.OriginalPresentationSiteMaps
public import Motivic.Cohomology.A1.RestrictionDifferenceRestriction

/-! # The constructed presentation lifts the exact original overlap section

Both successive target restrictions are composed with the literal original overlap
map. The point and the whole closed scheme over the retained base are preserved.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic Opposite
open AlgebraicGeometry.Scheme.RelativeCurve AlgebraicGeometry.Scheme.RelativeCurvePencil
open AlgebraicGeometry.Scheme.Hom

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation

variable {k : Type u} [Field k] {X Y A : SmoothSite (Spec (.of k))}
  [IsAffine X.left] [IsAffine Y.left] [IsAffine A.left]
  (p : Y ⟶ X) [Etale p.left] (a : A ⟶ X) [IsOpenImmersion a.left]
  {Z : Scheme.{u}} (z : Z ⟶ X.left) (s : Z ⟶ Y.left) (x : X.left)
  (e : OriginalEtalePresentation k X.hom p.left a.left z s x)

local instance : IsNoetherianRing e.base := e.base_noetherian
local instance : Smooth e.toField := e.base_smooth
local instance : IsAffine e.target := e.target_affine
local instance : IsOpenImmersion e.refinement := e.refinement_open
local instance : IsIntegral e.compact := e.compact_integral
local instance : IsLocallyNoetherian e.compact := e.compact_noetherian
local instance (c : e.compact) : IsIntegrallyClosed (e.compact.presheaf.stalk c) :=
  e.compact_normal c
local instance : IsFinite e.projectiveMap := e.projective_finite
local instance : IsOpenImmersion e.inclusion := e.inclusion_open
local instance : SmoothOfRelativeDimension 1
    (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) := e.target_smooth

/-- Actual local lifting on the original `Y ×[X] A`, preserving all point and
whole-boundary conditions supplied by the constructed presentation. -/
theorem exists_original_overlap_lifting
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) :
    ∃ U : e.target.Opens, IsAffineOpen U ∧ e.point ∈ U ∧
    ∃ (V : (Spec e.base).Opens) (hV : IsAffineOpen V),
      let : IsAffine V.toScheme := hV
      (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) e.point ∈ V ∧
      (∀ c : e.closed,
        (e.closedInclusion ≫ e.inclusion ≫ e.projectiveMap ≫
          ProjectiveSpace.toSpec e.base _) c ∈ V → e.closedInclusion c ∈ U) ∧
      ∃ hW : IsAffineOpen (boundaryBaseSourceOpen
          (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) U V),
        let : IsAffine (boundaryBaseSourceOpen
          (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) U V).toScheme := hW
        P.HasRestrictionDifferenceLifting
          (fixedTargetOverlapRestriction k e.base (ULift.{u} (Fin 2))
            e.target e.compact e.toField
            (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _)
            (pullback.snd p.left e.refinement) (pullback.snd a.left e.refinement)
            e.inclusion e.projectiveMap rfl U V ≫ overlapToOriginal p a z s x e)
          (fixedTargetPencilBeta k e.base (ULift.{u} (Fin 2))
            e.target e.compact e.toField
            (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _)
            (pullback.snd p.left e.refinement) (pullback.snd a.left e.refinement)
            e.inclusion e.projectiveMap rfl U V)
          (fixedTargetPencilAlpha k e.base (ULift.{u} (Fin 2))
            e.target e.compact e.toField
            (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _)
            (pullback.snd p.left e.refinement) (pullback.snd a.left e.refinement)
            e.inclusion e.projectiveMap rfl U V) := by
  obtain ⟨U, hU, hxU, V, hV, hxV, hclosed, hW, hL⟩ :=
    exists_lifting k (X := X.left) (Y := Y.left) (A := A.left)
      X.hom p.left a.left z s x e P hP
  let : IsAffine V.toScheme := hV
  let : IsAffine (boundaryBaseSourceOpen
      (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) U V).toScheme := hW
  refine ⟨U, hU, hxU, V, hV, hxV, hclosed, hW, ?_⟩
  have hL' := fixedTarget_originalOverlap_hasRestrictionDifferenceLifting
    k e.base (ULift.{u} (Fin 2)) e.target e.compact e.toField
    (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _)
    (pullback.snd p.left e.refinement) (pullback.snd a.left e.refinement)
    e.inclusion e.projectiveMap rfl U V P hL
  exact PresheafWithTransfers.HasRestrictionDifferenceLifting.restrict P hL'
    (overlapToOriginal p a z s x e)

end AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation
