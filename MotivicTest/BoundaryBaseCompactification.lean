module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.Compactification
/-! # Original cover, full boundary and fixed compactification after the actual shrink -/
set_option linter.hashCommand false
public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Hom
variable {S X Y Z C : Scheme.{u}} (q : X ⟶ S) (p : Y ⟶ X)
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z)
  (U : X.Opens) (V : S.Opens)
  (h : ∀ t : Z, (z ≫ q) t ∈ V → z t ∈ U)
  (π : C ⟶ S) (j : Y ⟶ C) (hj : j ≫ π = p ≫ q)
example (H : IsPullback s (𝟙 Z) p z) :
    IsPullback (boundaryBaseCoverLift q p z s hs U V h)
      (𝟙 (boundaryBaseClosedOpen q z V).toScheme)
      (boundaryBaseCoverMap q p U V) (boundaryBaseLift q z U V h) :=
  boundaryBaseCoverLift_isPullback q p z s hs U V h H
example [IsOpenImmersion j] : IsOpenImmersion (boundaryBaseCoverInclusion q p π j hj U V) :=
  boundaryBaseCoverInclusion_open q p π j hj U V
#print axioms boundaryBaseCoverLift_isPullback
#print axioms boundaryBaseCoverInclusion_open
#print axioms boundaryBaseCoverInclusion_smooth
#print axioms boundaryBaseProjectiveMap_finite
end AlgebraicGeometry.Scheme.Hom
