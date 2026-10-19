module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.CanonicalFrame
/-! # Actual affine simultaneous shrink and original canonical graph frame -/
set_option linter.hashCommand false
public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Hom
variable {S X Z : Scheme.{u}} (q : X ⟶ S) [IsSeparated q]
  [SmoothOfRelativeDimension 1 q] [IsAffine X] [IsAffine S]
  (z : Z ⟶ X) [IsFinite (z ≫ q)] (x : X)
example : ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
    ∃ V : S.Opens, IsAffineOpen V ∧ q x ∈ V ∧
    ∃ h : ∀ t : Z, (z ≫ q) t ∈ V → z t ∈ U,
      IsAffineOpen (boundaryBaseSourceOpen q U V) ∧
      Nonempty (SheafOfModules.unit
        (pullback (boundaryBaseSourceProjection q U V)
          (boundaryBaseLift q z U V h ≫ boundaryBaseSourceProjection q U V)).ringCatSheaf ≅
        idealModule (boundaryGraphTarget (boundaryBaseSourceProjection q U V)
          (boundaryBaseLift q z U V h))) :=
  exists_affine_boundaryBaseCanonicalFrame q z x
#print axioms exists_affine_boundaryBaseCanonicalFrame
#print axioms boundaryBaseCanonicalFrame_inclusion
#print axioms boundaryBaseGraph_isPullback
end AlgebraicGeometry.Scheme.Hom
