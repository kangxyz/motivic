/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.CoherentIdealCoordinate
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.Prescribed.AmbientCoordinate

/-! # Original graph coordinates in the same prescribed affine extension

The actual glued ideal frame, already compatible with the original dual frame,
is extended once. Its infinity and marked coordinates remain unchanged.


Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.PrescribedGraphCoordinate`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.RetainedTargetPrescribedScalar`,
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Norm.PrescribedGraphMarked`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Hom
variable {S X Y Z C D : Scheme.{u}} (q : X ⟶ S) [IsSeparated q]
  [SmoothOfRelativeDimension 1 q] (qC : C ⟶ S) [IsSeparated qC]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ qC)]
  (p : Y ⟶ X) [Flat p] (hq : j ≫ qC = p ≫ q)
  (z : Z ⟶ X) (s : Z ⟶ Y) (h : s ≫ p = z) (H : IsPullback s (𝟙 _) p z)
  (e : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
    idealModule (boundaryGraphTarget q z))
  (d : D ⟶ C) (hd : Disjoint (Set.range j) (Set.range d))


variable (A : (pullback (j ≫ qC) qC).affineOpens)
  (b : (pullback (pullback.snd (j ≫ qC) qC) d ⨿ pullback (j ≫ qC) (s ≫ j ≫ qC)) ⟶
    A.val.toScheme)
  (hc : b ≫ A.val.ι =
    coprod.desc (infinityProductMap qC j d) (graphBoundaryRestriction qC j s))
  (E : PrescribedAffineFrameExtension A b (relativeCompactificationGraphLine qC j)
    ((Modules.pullbackComp b A.val.ι).app (relativeCompactificationGraphLine qC j).val ≪≫
      (Modules.pullbackCongr hc).app (relativeCompactificationGraphLine qC j).val ≪≫
      relativeFullBoundaryIdealFrame q qC j p hq z s h H e d hd))

/-- The given original graph functional has the exact original full coordinate
on the full boundary of the SAME prescribed extension. -/
theorem prescribedGraphFrame_full_coordinate :
    unitEndomorphismPullback E.boundaryLift
      (E.frame.inv ≫ pullbackUnitMap E.inclusion
        (pullbackUnitMap A.val.ι (idealInclusion (compactificationGraph qC j)))) =
      relativeFullBoundaryCoordinate q qC j p hq z s h H e d hd := by
  rw [prescribedExtension_original_coordinate A b _ hc
    (relativeCompactificationGraphLine qC j)
    (relativeFullBoundaryIdealFrame q qC j p hq z s h H e d hd) E]
  exact relativeFullBoundaryIdealFrame_coordinate q qC j p hq z s h H e d hd

/-- Full infinity, including its scheme-theoretic thickening, retains value one. -/
theorem prescribedGraphFrame_infinity_coordinate :
    unitEndomorphismPullback (coprod.inl ≫ E.boundaryLift)
      (E.frame.inv ≫ pullbackUnitMap E.inclusion
        (pullbackUnitMap A.val.ι (idealInclusion (compactificationGraph qC j)))) = 𝟙 _ := by
  rw [← unitEndomorphismPullback_comp, prescribedGraphFrame_full_coordinate]
  exact relativeFullBoundaryCoordinate_inl q qC j p hq z s h H e d hd

/-- The marked coordinate remains that of the SAME supplied target ideal frame. -/
theorem prescribedGraphFrame_marked_coordinate :
    unitEndomorphismPullback (coprod.inr ≫ E.boundaryLift)
      (E.frame.inv ≫ pullbackUnitMap E.inclusion
        (pullbackUnitMap A.val.ι (idealInclusion (compactificationGraph qC j)))) =
    unitEndomorphismPullback
      ((relativeBoundaryProductIso q qC j p hq z s h).hom ≫ boundaryProductMap q p z)
      (e.hom ≫ idealInclusion (boundaryGraphTarget q z)) := by
  rw [← unitEndomorphismPullback_comp, prescribedGraphFrame_full_coordinate]
  exact relativeFullBoundaryCoordinate_inr q qC j p hq z s h H e d hd

/-- An actual map through the full infinity component gives scalar one. The
only comparison premise is an equality of original ambient scheme maps. -/
theorem prescribedGraphFrame_infinity_scalar_of_ambient_eq
    {T : Scheme.{u}} (k : T ⟶ E.neighborhood)
    (r : T ⟶ pullback (pullback.snd (j ≫ qC) qC) d)
    (he : k ≫ E.ambientInclusion = r ≫ infinityProductMap qC j d) :
    k.appTop (Modules.Hom.app
      (E.frame.inv ≫ pullbackUnitMap E.inclusion
        (pullbackUnitMap A.val.ι (idealInclusion (compactificationGraph qC j)))) ⊤
      (1 : Γ(E.neighborhood, ⊤))) = 1 := by
  have hE : E.boundaryLift ≫ E.ambientInclusion =
      coprod.desc (infinityProductMap qC j d) (graphBoundaryRestriction qC j s) := by
    simpa only [PrescribedAffineFrameExtension.ambientInclusion, Category.assoc] using
      (congrArg (fun l => l ≫ A.val.ι) E.boundary_eq).trans hc
  have hk : k = r ≫ coprod.inl ≫ E.boundaryLift := by
    apply (cancel_mono E.ambientInclusion).mp
    simpa only [Category.assoc, hE, coprod.inl_desc] using he
  rw [← unitEndomorphismPullback_app_one]
  have hu : unitEndomorphismPullback k
      (E.frame.inv ≫ pullbackUnitMap E.inclusion
        (pullbackUnitMap A.val.ι (idealInclusion (compactificationGraph qC j)))) = 𝟙 _ := by
    rw [hk, ← unitEndomorphismPullback_comp, prescribedGraphFrame_infinity_coordinate]
    simp [unitEndomorphismPullback]
  rw [hu]
  rfl

/-- An actual marked factorization evaluates the SAME supplied target frame,
with no normalization to a chosen affine coordinate. -/
theorem prescribedGraphFrame_marked_scalar_of_ambient_eq
    {T : Scheme.{u}} (k : T ⟶ E.neighborhood)
    (r : T ⟶ pullback (j ≫ qC) (s ≫ j ≫ qC))
    (he : k ≫ E.ambientInclusion = r ≫ graphBoundaryRestriction qC j s) :
    k.appTop (Modules.Hom.app
      (E.frame.inv ≫ pullbackUnitMap E.inclusion
        (pullbackUnitMap A.val.ι (idealInclusion (compactificationGraph qC j)))) ⊤
      (1 : Γ(E.neighborhood, ⊤))) =
    Modules.Hom.app (unitEndomorphismPullback
      (r ≫ (relativeBoundaryProductIso q qC j p hq z s h).hom ≫ boundaryProductMap q p z)
      (e.hom ≫ idealInclusion (boundaryGraphTarget q z))) ⊤ (1 : Γ(T, ⊤)) := by
  have hE : E.boundaryLift ≫ E.ambientInclusion =
      coprod.desc (infinityProductMap qC j d) (graphBoundaryRestriction qC j s) := by
    simpa only [PrescribedAffineFrameExtension.ambientInclusion, Category.assoc] using
      (congrArg (fun l => l ≫ A.val.ι) E.boundary_eq).trans hc
  have hk : k = r ≫ coprod.inr ≫ E.boundaryLift := by
    apply (cancel_mono E.ambientInclusion).mp
    simpa only [Category.assoc, hE, coprod.inr_desc] using he
  rw [← unitEndomorphismPullback_app_one, hk, ← unitEndomorphismPullback_comp,
    prescribedGraphFrame_marked_coordinate, unitEndomorphismPullback_comp]

end AlgebraicGeometry.Scheme.Hom
