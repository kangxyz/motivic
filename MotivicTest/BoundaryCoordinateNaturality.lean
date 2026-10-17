module
import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.CoordinateProductPullback
import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.FixedOpenBoundaryUnit

/-! # Direct tests for the literal fixed-source boundary unit and its pullback -/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open Scheme.Hom
universe u

section
variable (R B : Type u) [CommRing R] [CommRing B] (z : R[X] →+* B)
  (U : (Spec (.of R[X])).Opens)
  (hU : Disjoint (U : Set (Spec (.of R[X]))) (Set.range (boundaryCoordinateMap R B z)))

example : IsIso (boundaryCoordinateEndomorphism R B z
    (boundaryProductMap (boundaryLineProjection R) U.ι (boundaryCoordinateMap R B z))) :=
  boundaryCoordinateEndomorphism_open_isIso R B z U hU

example {Y : Scheme.{u}} (p : Y ⟶ U.toScheme) :
    boundaryCoordinateEndomorphism R B z
        (boundaryProductMap (boundaryLineProjection R) (p ≫ U.ι) (boundaryCoordinateMap R B z)) =
      unitEndomorphismPullback
        (boundarySourceProductMap (boundaryLineProjection R) U.ι p (boundaryCoordinateMap R B z))
        (boundaryCoordinateEndomorphism R B z
          (boundaryProductMap (boundaryLineProjection R) U.ι (boundaryCoordinateMap R B z))) :=
  boundaryCoordinateEndomorphism_sourceProduct R B z U.ι p

example {Y : Scheme.{u}} (p : Y ⟶ U.toScheme) :
    IsIso (boundaryCoordinateEndomorphism R B z
      (boundaryProductMap (boundaryLineProjection R) (p ≫ U.ι) (boundaryCoordinateMap R B z))) := by
  have := boundaryCoordinateEndomorphism_open_isIso R B z U hU
  rw [boundaryCoordinateEndomorphism_sourceProduct R B z U.ι p]
  unfold unitEndomorphismPullback
  infer_instance
end
