module
import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Refinement.Coordinate
import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Refinement.Boundary.Maps
/-! # Strict consumers of the original whole-boundary relative coordinate comparison -/
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.RelativeProjectiveLine

example (R : Type) [CommRing R] (V : (Spec (.of (Polynomial R))).Opens) (r : R)
    (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V) :
    Scheme.Hom.unitEndomorphismPullback (commonNeighborhoodBoundaryToGraph R V r hV)
      (neighborhoodBoundaryCoordinate R V hV) =
    Scheme.Hom.unitEndomorphismPullback (commonNeighborhoodBoundaryToPsi R V r)
      (fixedPsiBoundaryUnit R V r).hom :=
  commonNeighborhoodBoundary_coordinate_eq R V r hV

example (R : Type) [CommRing R] (V : (Spec (.of (Polynomial R))).Opens) (r : R)
    (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V) :
    commonNeighborhoodBoundaryToGraph R V r hV ≫ neighborhoodGraphBoundaryMap R V hV =
      commonNeighborhoodBoundaryMap R V r ≫ commonNeighborhoodToGraphAmbient R V r :=
  commonNeighborhoodBoundaryToGraph_fac R V r hV

example (R : Type) [CommRing R] (V : (Spec (.of (Polynomial R))).Opens) (r : R) :
    commonNeighborhoodBoundaryToPsi R V r ≫ fixedPsiBoundaryMap R r V =
      commonNeighborhoodBoundaryMap R V r ≫ commonNeighborhoodToPsiAmbient R V r :=
  commonNeighborhoodBoundaryToPsi_fac R V r
