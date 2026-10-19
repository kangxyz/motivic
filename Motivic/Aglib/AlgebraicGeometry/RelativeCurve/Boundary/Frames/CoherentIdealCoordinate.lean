/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.CoherentIdealFrame
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.IdealFrameBoundaryScalar

/-! # The same full ideal-frame coordinate and its actual component values

Genuine ideal/dual frame compatibility identifies the original ideal functional
coordinate with the already chosen full-boundary coordinate. Its infinity and
marked restrictions therefore preserve the existing section choices literally.


Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.CoherentIdealCoordinate`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.PrescribedGraphCoordinate`,
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Data.NativeSimultaneousSectionChoice`.
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

omit [SmoothOfRelativeDimension 1 (j ≫ qC)] in
/-- Both actual component frame equations are retained by the same ideal gluing. -/
theorem relativeFullBoundaryIdealFrame_component_equations :
    let a := infinityProductMap qC j d
    let b := graphBoundaryRestriction qC j s
    let I := idealModule (compactificationGraph qC j)
    let E := relativeFullBoundaryIdealFrame q qC j p hq z s h H e d hd
    (Modules.restrictFunctor (coprod.inl : _ ⟶ _)).map E.hom ≫
        (restrictUnitIso _).hom = (coprodPullbackRestrictLeft a b).hom.app I ≫
          (infinityBoundaryIdealIso qC j d hd).inv ∧
    (Modules.restrictFunctor (coprod.inr : _ ⟶ _)).map E.hom ≫
        (restrictUnitIso _).hom = (coprodPullbackRestrictRight a b).hom.app I ≫
          (relativeCompactificationBoundaryFrame q qC j p hq z s h H e).inv := by
  dsimp only
  exact Classical.choose_spec (exists_coprod_pullback_unitIso
    (infinityProductMap qC j d) (graphBoundaryRestriction qC j s)
    (idealModule (compactificationGraph qC j))
    (infinityBoundaryIdealIso qC j d hd).symm
    (relativeCompactificationBoundaryFrame q qC j p hq z s h H e).symm)

/-- The SAME full ideal frame gives the EXISTING canonical full-boundary coordinate. -/
theorem relativeFullBoundaryIdealFrame_coordinate :
    (relativeFullBoundaryIdealFrame q qC j p hq z s h H e d hd).inv ≫
      pullbackUnitMap
        (coprod.desc (infinityProductMap qC j d) (graphBoundaryRestriction qC j s))
        (idealInclusion (compactificationGraph qC j)) =
      relativeFullBoundaryCoordinate q qC j p hq z s h H e d hd := by
  have hc := dualBoundaryTrivialization_canonical
    (coprod.desc (infinityProductMap qC j d) (graphBoundaryRestriction qC j s))
    (relativeCompactificationGraphLine qC j) (idealInclusion (compactificationGraph qC j))
    (relativeFullBoundaryIdealFrame q qC j p hq z s h H e d hd).symm
  rw [relativeFullBoundaryIdealFrame_dual_eq] at hc
  exact hc.symm

/-- Literal infinity restriction of the original IDEAL functional equals one. -/
theorem relativeFullBoundaryIdealFrame_infinity_coordinate :
    unitEndomorphismPullback coprod.inl
      ((relativeFullBoundaryIdealFrame q qC j p hq z s h H e d hd).inv ≫
        pullbackUnitMap
          (coprod.desc (infinityProductMap qC j d) (graphBoundaryRestriction qC j s))
          (idealInclusion (compactificationGraph qC j))) = 𝟙 _ := by
  rw [relativeFullBoundaryIdealFrame_coordinate]
  exact relativeFullBoundaryCoordinate_inl q qC j p hq z s h H e d hd

/-- Literal marked restriction keeps the SAME supplied target ideal frame. -/
theorem relativeFullBoundaryIdealFrame_marked_coordinate :
    unitEndomorphismPullback coprod.inr
      ((relativeFullBoundaryIdealFrame q qC j p hq z s h H e d hd).inv ≫
        pullbackUnitMap
          (coprod.desc (infinityProductMap qC j d) (graphBoundaryRestriction qC j s))
          (idealInclusion (compactificationGraph qC j))) =
    unitEndomorphismPullback
      ((relativeBoundaryProductIso q qC j p hq z s h).hom ≫ boundaryProductMap q p z)
      (e.hom ≫ idealInclusion (boundaryGraphTarget q z)) := by
  rw [relativeFullBoundaryIdealFrame_coordinate]
  exact relativeFullBoundaryCoordinate_inr q qC j p hq z s h H e d hd

end AlgebraicGeometry.Scheme.Hom
