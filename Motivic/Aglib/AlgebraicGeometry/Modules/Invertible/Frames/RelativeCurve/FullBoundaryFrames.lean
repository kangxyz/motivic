module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.RelativeCurve.CompactificationBoundaryFrame
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.RelativeCurve.BoundaryFrameUnit
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Graph.Retained
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.InfinityBoundaryIdeal
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.DisjointBoundary.UnitAutomorphism
/-! # Prescribed whole-boundary frames for relative-curve pencils -/
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

/-- Dualize the actual transported ideal frame, retaining its literal functional. -/
def relativeCompactificationDivisorFrame :
    (Scheme.Modules.pullback (graphBoundaryRestriction qC j s)).obj
      (dualLineBundle _ (relativeCompactificationGraphLine qC j)).val ≅
        SheafOfModules.unit (pullback (j ≫ qC) (s ≫ j ≫ qC)).ringCatSheaf :=
  dualBoundaryTrivialization _ (relativeCompactificationGraphLine qC j)
    (relativeCompactificationBoundaryFrame q qC j p hq z s h H e)

/-- Glue the canonical infinity frame and the specified original full-boundary frame.
Smoothness is used only on the retained open curve, never on its compactification. -/
theorem exists_relativeFullBoundaryDivisorFrame (d : D ⟶ C)
    (hd : Disjoint (Set.range j) (Set.range d)) :
    let L := (dualLineBundle _ (relativeCompactificationGraphLine qC j)).val
    let a := infinityProductMap qC j d
    let b := graphBoundaryRestriction qC j s
    ∃ E : (Scheme.Modules.pullback (coprod.desc a b)).obj L ≅
        SheafOfModules.unit ((pullback (pullback.snd (j ≫ qC) qC) d ⨿
          pullback (j ≫ qC) (s ≫ j ≫ qC))).ringCatSheaf,
      (Scheme.Modules.restrictFunctor (coprod.inl : pullback (pullback.snd (j ≫ qC) qC) d ⟶
        pullback (pullback.snd (j ≫ qC) qC) d ⨿ pullback (j ≫ qC) (s ≫ j ≫ qC))).map E.hom ≫
          (restrictUnitIso _).hom =
        (coprodPullbackRestrictLeft a b).hom.app L ≫
          (infinityBoundaryDivisorIso qC j d hd
            (relativeCompactificationGraphLine qC j).property).hom ∧
      (Scheme.Modules.restrictFunctor (coprod.inr : pullback (j ≫ qC) (s ≫ j ≫ qC) ⟶
        pullback (pullback.snd (j ≫ qC) qC) d ⨿ pullback (j ≫ qC) (s ≫ j ≫ qC))).map E.hom ≫
          (restrictUnitIso _).hom =
        (coprodPullbackRestrictRight a b).hom.app L ≫
          (relativeCompactificationDivisorFrame q qC j p hq z s h H e).hom := by
  dsimp only
  exact exists_coprod_pullback_unitIso _ _ _
    (infinityBoundaryDivisorIso qC j d hd (relativeCompactificationGraphLine qC j).property)
    (relativeCompactificationDivisorFrame q qC j p hq z s h H e)

omit [SmoothOfRelativeDimension 1 q] in
/-- The fixed punctured source gets the original scalar at Z and identity at infinity. -/
theorem exists_relativeFixedBoundaryUnit {A : Scheme.{u}} (a : A ⟶ X) [Flat a]
    (ha : Disjoint (Set.range a) (Set.range z)) (d : D ⟶ S) :
    let B := pullback (a ≫ q) d
    let W := pullback (a ≫ q) (z ≫ q)
    ∃ E : SheafOfModules.unit (B ⨿ W).ringCatSheaf ≅
        SheafOfModules.unit (B ⨿ W).ringCatSheaf,
      (Scheme.Modules.restrictFunctor (coprod.inl : B ⟶ B ⨿ W)).map E.hom = 𝟙 _ ∧
      (Scheme.Modules.restrictFunctor (coprod.inr : W ⟶ B ⨿ W)).map E.hom ≫
        (restrictUnitIso _).hom = (restrictUnitIso _).hom ≫
          unitEndomorphismPullback (boundaryProductMap q a z)
            (e.hom ≫ idealInclusion (boundaryGraphTarget q z)) := by
  have := relativeBoundaryFrame_scalar_isIso q a z e ha
  exact exists_coprod_unitAutomorphism _ _ (asIso
    (unitEndomorphismPullback (boundaryProductMap q a z)
      (e.hom ≫ idealInclusion (boundaryGraphTarget q z))))
end AlgebraicGeometry.Scheme.Hom
