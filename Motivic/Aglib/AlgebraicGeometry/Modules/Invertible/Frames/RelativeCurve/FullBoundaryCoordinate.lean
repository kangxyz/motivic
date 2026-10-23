/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.RelativeCurve.FullBoundaryFrames
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.CoproductUnitEndomorphism
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.BoundaryCanonicalCoordinate
/-! # Literal canonical coordinates in the original relative whole-boundary frame -/
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

/-- Choose a frame on the full boundary with the prescribed infinity and graph restrictions. -/
def relativeFullBoundaryFrame := Classical.choose
  (exists_relativeFullBoundaryDivisorFrame q qC j p hq z s h H e d hd)

/-- Express the pulled canonical dual section in the chosen full-boundary frame. -/
def relativeFullBoundaryCoordinate :=
  pullbackSectionMap (coprod.desc (infinityProductMap qC j d) (graphBoundaryRestriction qC j s))
    (canonicalDualHom _ (relativeCompactificationGraphLine qC j).val
      (idealInclusion (compactificationGraph qC j))) ≫
        (relativeFullBoundaryFrame q qC j p hq z s h H e d hd).hom

omit d hd in
/-- This is the original canonical section, not merely an isomorphic divisor class. -/
theorem relativeCompactificationDivisorFrame_coordinate :
    pullbackCanonicalDualHom (graphBoundaryRestriction qC j s)
      (relativeCompactificationGraphLine qC j) (idealInclusion (compactificationGraph qC j)) ≫
        (relativeCompactificationDivisorFrame q qC j p hq z s h H e).hom =
    unitEndomorphismPullback
      ((relativeBoundaryProductIso q qC j p hq z s h).hom ≫ boundaryProductMap q p z)
      (e.hom ≫ idealInclusion (boundaryGraphTarget q z)) := by
  rw [relativeCompactificationDivisorFrame, dualBoundaryTrivialization_canonical]
  exact relativeCompactificationBoundaryFrame_coordinate q qC j p hq z s h H e

/-- The chosen whole-boundary coordinate is literally one on the entire infinity component. -/
theorem relativeFullBoundaryCoordinate_inl :
    unitEndomorphismPullback coprod.inl
      (relativeFullBoundaryCoordinate q qC j p hq z s h H e d hd) = 𝟙 _ := by
  have hE := (Classical.choose_spec
    (exists_relativeFullBoundaryDivisorFrame q qC j p hq z s h H e d hd)).1
  have hc := unitEndomorphismPullback_coprod_inl_coordinate
    (infinityProductMap qC j d) (graphBoundaryRestriction qC j s)
    (dualLineBundle _ (relativeCompactificationGraphLine qC j)).val
    (canonicalDualHom _ (relativeCompactificationGraphLine qC j).val
      (idealInclusion (compactificationGraph qC j)))
    (relativeFullBoundaryFrame q qC j p hq z s h H e d hd)
    (infinityBoundaryDivisorIso qC j d hd (relativeCompactificationGraphLine qC j).property) hE
  exact hc.trans (infinityBoundaryDivisorIso_canonical qC j d hd
    (relativeCompactificationGraphLine qC j).property)

/-- The chosen whole-boundary coordinate retains the exact original target scalar on Z. -/
theorem relativeFullBoundaryCoordinate_inr :
    unitEndomorphismPullback coprod.inr
      (relativeFullBoundaryCoordinate q qC j p hq z s h H e d hd) =
    unitEndomorphismPullback
      ((relativeBoundaryProductIso q qC j p hq z s h).hom ≫ boundaryProductMap q p z)
      (e.hom ≫ idealInclusion (boundaryGraphTarget q z)) := by
  have hE := (Classical.choose_spec
    (exists_relativeFullBoundaryDivisorFrame q qC j p hq z s h H e d hd)).2
  have hc := unitEndomorphismPullback_coprod_inr_coordinate
    (infinityProductMap qC j d) (graphBoundaryRestriction qC j s)
    (dualLineBundle _ (relativeCompactificationGraphLine qC j)).val
    (canonicalDualHom _ (relativeCompactificationGraphLine qC j).val
      (idealInclusion (compactificationGraph qC j)))
    (relativeFullBoundaryFrame q qC j p hq z s h H e d hd)
    (relativeCompactificationDivisorFrame q qC j p hq z s h H e) hE
  exact hc.trans (relativeCompactificationDivisorFrame_coordinate q qC j p hq z s h H e)
end AlgebraicGeometry.Scheme.Hom
