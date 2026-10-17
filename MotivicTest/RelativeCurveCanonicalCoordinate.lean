module
import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.FullBoundaryCoordinate
/-! # Original canonical graph section on both full boundary components -/
set_option linter.hashCommand false
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

example :
    unitEndomorphismPullback coprod.inl
      (relativeFullBoundaryCoordinate q qC j p hq z s h H e d hd) = 𝟙 _ :=
  relativeFullBoundaryCoordinate_inl q qC j p hq z s h H e d hd
example :
    unitEndomorphismPullback coprod.inr
      (relativeFullBoundaryCoordinate q qC j p hq z s h H e d hd) =
    unitEndomorphismPullback
      ((relativeBoundaryProductIso q qC j p hq z s h).hom ≫ boundaryProductMap q p z)
      (e.hom ≫ idealInclusion (boundaryGraphTarget q z)) :=
  relativeFullBoundaryCoordinate_inr q qC j p hq z s h H e d hd
#print axioms relativeFullBoundaryCoordinate_inl
#print axioms relativeFullBoundaryCoordinate_inr
end AlgebraicGeometry.Scheme.Hom
