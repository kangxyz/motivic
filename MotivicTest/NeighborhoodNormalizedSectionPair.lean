module
import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Sections.NormalizedPair
/-! Native dual normalization retains both original whole zero divisors. -/
set_option linter.hashCommand false
open CategoryTheory AlgebraicGeometry RelativeProjectiveLine
open Scheme.Modules Scheme.Modules.Invertible
universe u
variable (R : Type u) [CommRing R]
variable (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme]
example (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)
    (r : R) (n : ℕ) (e : neighborhoodFrame R V r n)
    (d : NeighborhoodSectionPair R V hV r n e) :
    NeighborhoodOpenSectionFiniteFlat R V r (neighborhoodSectionOpen R V r)
      (neighborhoodSerreOpen_eq_compact R V r)
      (tensorLineBundle _ (neighborhoodLocalTwist R V r n)
        (dualLineBundle _ (neighborhoodLocalIdeal R V r))) d.normalizedNumerator :=
  d.normalizedNumerator_finite_flat
#print axioms NeighborhoodSectionPair.normalizedNumerator_finite_flat
#print axioms NeighborhoodSectionPair.normalizedDenominator_finite_flat
