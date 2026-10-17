module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.BoundaryBaseSourceBoundary
/-! # Full original Z and original target boundary after the actual parameter shrink -/
set_option linter.hashCommand false
public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Hom
variable {S X Y Z C D : Scheme.{u}} (q : X ⟶ S) (p : Y ⟶ X)
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z)
  (π : C ⟶ S) (j : Y ⟶ C) (hj : j ≫ π = p ≫ q) (d : D ⟶ C)
  (U : X.Opens) (V : S.Opens)
  (h : ∀ t : Z, (z ≫ q) t ∈ V → z t ∈ U)
example : IsPullback (boundaryBaseClosedOpen q z V).ι
    (boundaryBaseCoverLift q p z s hs U V h ≫
      boundaryBaseCoverInclusion q p π j hj U V)
    (s ≫ j) (pullback.snd V.ι π) :=
  boundaryBaseSourceZero_isPullback q p z s hs π j hj U V h
example [IsClosedImmersion (s ≫ j)] :
    IsClosedImmersion (boundaryBaseCoverLift q p z s hs U V h ≫
      boundaryBaseCoverInclusion q p π j hj U V) :=
  boundaryBaseSourceZero_closed q p z s hs π j hj U V h
example [IsFinite (z ≫ q)] :
    IsFinite ((boundaryBaseCoverLift q p z s hs U V h ≫
      boundaryBaseCoverInclusion q p π j hj U V) ≫ pullback.fst V.ι π) :=
  boundaryBaseSourceZero_finite q p z s hs π j hj U V h
example : boundaryBaseSourceBoundaryToFull q p z s hs π j hj d V ≫
    boundaryBaseWholeMap π (coprod.desc d (s ≫ j)) V =
      coprod.desc (boundaryBaseWholeMap π d V)
        (boundaryBaseCoverLift q p z s hs U V h ≫
          boundaryBaseCoverInclusion q p π j hj U V) :=
  boundaryBaseSourceBoundaryToFull_boundary q p z s hs π j hj d U V h
#print axioms boundaryBaseSourceZero_isPullback
#print axioms boundaryBaseSourceZero_closed
#print axioms boundaryBaseSourceZero_finite
#print axioms boundaryBaseSourceBoundaryFrame
end AlgebraicGeometry.Scheme.Hom
