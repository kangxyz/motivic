module
import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Boundary.Projection
/-! Whole original boundary projection, including the literal original zero. -/
set_option linter.hashCommand false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RelativeProjectiveLine
universe u
variable (R : Type u) [CommRing R]
variable (V : (Spec (.of (Polynomial R))).Opens)
variable (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)
example : neighborhoodGraphBoundaryMap R V hV ≫ pullback.snd _ _ =
    neighborhoodGraphBoundaryToOriginal R V hV ≫ fullNeighborhoodBoundaryMap R V :=
  neighborhoodGraphBoundaryToOriginal_fac R V hV
#print axioms neighborhoodGraphBoundaryToOriginal_fac
#print axioms neighborhoodGraphBoundaryToProduct
