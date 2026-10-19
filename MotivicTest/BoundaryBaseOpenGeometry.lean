module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.OpenGeometry
/-! # The actual full finite boundary after simultaneous source and base shrinking -/
set_option linter.hashCommand false
public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Hom
variable {S X Z : Scheme.{u}} (q : X ⟶ S) (z : Z ⟶ X)
  (U : X.Opens) (V : S.Opens)
  (h : ∀ t : Z, (z ≫ q) t ∈ V → z t ∈ U)
example [IsFinite (z ≫ q)] :
    IsFinite (boundaryBaseLift q z U V h ≫ boundaryBaseSourceProjection q U V) :=
  boundaryBaseLift_finite q z U V h
example : IsPullback (boundaryBaseLift q z U V h) (boundaryBaseClosedOpen q z V).ι
    (boundaryBaseSourceOpen q U V).ι z := boundaryBaseLift_isPullback q z U V h
#print axioms boundaryBaseLift_isPullback
#print axioms boundaryBaseLift_finite
#print axioms boundaryBaseSourceProjection_smooth
#print axioms boundaryBaseSourceOpen_affine
end AlgebraicGeometry.Scheme.Hom
