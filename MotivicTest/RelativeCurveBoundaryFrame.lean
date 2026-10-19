module
import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.RelativeCurve.BoundaryFramePullback
/-! # Full finite-boundary frames on arbitrary smooth relative curves -/
set_option linter.hashCommand false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Hom
variable {S X Y Z : Scheme.{u}} (q : X ⟶ S) [IsSeparated q]
  [SmoothOfRelativeDimension 1 q] (z : Z ⟶ X)
example [IsAffine X] [IsFinite (z ≫ q)] (points : Set X) (hpoints : points.Finite) :
    ∃ U : X.Opens, points ⊆ U ∧
      Nonempty ((idealModule (boundaryGraphTarget q z)).restrict
        ((pullback.fst q (z ≫ q)) ⁻¹ᵁ U).ι ≅
          SheafOfModules.unit ((pullback.fst q (z ≫ q)) ⁻¹ᵁ U).toScheme.ringCatSheaf) :=
  exists_relativeBoundaryFrame_around_finite q z points hpoints
example (p : Y ⟶ X) [Flat p] (s : Z ⟶ Y) (h : s ≫ p = z)
    (H : IsPullback s (𝟙 _) p z)
    (e : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
      idealModule (boundaryGraphTarget q z)) :
    (relativeNeighborhoodBoundaryFrame q p z s h H e).hom ≫
        idealInclusion (boundaryGraphSource q p z s h) =
      unitEndomorphismPullback (boundaryProductMap q p z)
        (e.hom ≫ idealInclusion (boundaryGraphTarget q z)) :=
  relativeNeighborhoodBoundaryFrame_inclusion q p z s h H e
#print axioms exists_relativeBoundaryFrame_around_finite
#print axioms relativeNeighborhoodBoundaryFrame_inclusion
end AlgebraicGeometry.Scheme.Hom
