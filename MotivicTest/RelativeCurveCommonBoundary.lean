module
import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Common.BoundaryCoordinate
/-! # Literal relative whole-boundary agreement on the actual source-change products -/
set_option linter.hashCommand false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil
variable {S X Y A B Z C D : Scheme.{u}}
  (q : X ⟶ S) [IsSeparated q] (π : C ⟶ S) (a : A ⟶ X) [Flat a]
  (z : Z ⟶ X)
  (e : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
    Hom.idealModule (Hom.boundaryGraphTarget q z))
  (ha : Disjoint (Set.range a) (Set.range z)) (d : D ⟶ C)
variable [SmoothOfRelativeDimension 1 q] [IsSeparated π]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
  (p : Y ⟶ X) [Flat p] (hq : j ≫ π = p ≫ q)
  (α : B ⟶ Y) (β : B ⟶ A) (h : α ≫ p = β ≫ a)
  (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 _) p z)
  (hd : Disjoint (Set.range j) (Set.range d))

example :
    Hom.unitEndomorphismPullback (commonBoundaryToLambda π j α s d)
      (Hom.relativeFullBoundaryCoordinate q π j p hq z s hs H e d hd) =
    Hom.unitEndomorphismPullback (commonBoundaryToPsi q π j p hq a α β h z s hs d)
      (fixedProductBoundaryFrame q π a z e ha d).hom :=
  commonBoundary_coordinate_eq q π a z e ha d j p hq α β h s hs H hd
#print axioms commonBoundary_coordinate_eq
#print axioms commonToLambda_isPullback
#print axioms commonToPsi_isPullback
end AlgebraicGeometry.Scheme.RelativeCurvePencil
