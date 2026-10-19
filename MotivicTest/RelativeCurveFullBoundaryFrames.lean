module
import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.RelativeCurve.FullBoundaryFrames
/-! # Actual whole-boundary frames, with no smooth compactification premise -/
set_option linter.hashCommand false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Hom
variable {S X Y Z C D A : Scheme.{u}} (q : X ⟶ S) [IsSeparated q]
  [SmoothOfRelativeDimension 1 q] (qC : C ⟶ S) [IsSeparated qC]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ qC)]
  (p : Y ⟶ X) [Flat p] (hq : j ≫ qC = p ≫ q)
  (z : Z ⟶ X) (s : Z ⟶ Y) (h : s ≫ p = z) (H : IsPullback s (𝟙 _) p z)
  (e : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
    idealModule (boundaryGraphTarget q z))
example (d : D ⟶ C) (hd : Disjoint (Set.range j) (Set.range d)) :
    Nonempty ((Scheme.Modules.pullback
      (coprod.desc (infinityProductMap qC j d) (graphBoundaryRestriction qC j s))).obj
        (dualLineBundle _ (relativeCompactificationGraphLine qC j)).val ≅
      SheafOfModules.unit ((pullback (pullback.snd (j ≫ qC) qC) d ⨿
        pullback (j ≫ qC) (s ≫ j ≫ qC))).ringCatSheaf) := by
  obtain ⟨E, _, _⟩ := exists_relativeFullBoundaryDivisorFrame q qC j p hq z s h H e d hd
  exact ⟨E⟩
example :
    (relativeCompactificationBoundaryFrame q qC j p hq z s h H e).hom ≫
      Modules.Hom.pullbackToUnit (idealInclusion (compactificationGraph qC j))
        (graphBoundaryRestriction qC j s) =
      unitEndomorphismPullback
        ((relativeBoundaryProductIso q qC j p hq z s h).hom ≫ boundaryProductMap q p z)
        (e.hom ≫ idealInclusion (boundaryGraphTarget q z)) :=
  relativeCompactificationBoundaryFrame_coordinate q qC j p hq z s h H e
omit [SmoothOfRelativeDimension 1 q] in
example (a : A ⟶ X) [Flat a] (ha : Disjoint (Set.range a) (Set.range z)) :
    IsIso (unitEndomorphismPullback (boundaryProductMap q a z)
      (e.hom ≫ idealInclusion (boundaryGraphTarget q z))) :=
  relativeBoundaryFrame_scalar_isIso q a z e ha
#print axioms exists_relativeFullBoundaryDivisorFrame
#print axioms exists_relativeFixedBoundaryUnit
#print axioms relativeCompactificationBoundaryFrame_coordinate
#print axioms relativeCompactificationGraphLine
end AlgebraicGeometry.Scheme.Hom
