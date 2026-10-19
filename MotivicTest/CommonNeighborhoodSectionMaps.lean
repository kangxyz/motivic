module
import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Refinement.Cartesian
/-! The actual common source lands in the original single-shrink section domain. -/
set_option linter.hashCommand false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RelativeProjectiveLine
universe u
variable (R : Type u) [CommRing R]
  (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme] (r : R)
example : IsOpenImmersion (commonNeighborhoodToSectionAmbient R V r) := inferInstance
example (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V) :
    commonNeighborhoodBoundaryToSection R V r hV ≫
      (neighborhoodGraphBoundaryMap R V hV ∣_
        ((neighborhoodProjectiveIso R V).hom ⁻¹ᵁ neighborhoodSerreOpen R V r)) =
    commonNeighborhoodBoundaryMap R V r ≫ commonNeighborhoodToSectionAmbient R V r :=
  commonNeighborhoodBoundaryToSection_fac R V r hV
#print axioms commonNeighborhoodBoundaryToSection_fac
#print axioms commonNeighborhoodToGraphAmbient_isPullback
#print axioms commonNeighborhoodToPsiAmbient_isPullback
