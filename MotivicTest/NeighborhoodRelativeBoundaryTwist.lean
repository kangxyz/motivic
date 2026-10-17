module
import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.NeighborhoodRelativeBoundaryTwist
/-! Actual all-degree units use only one original base shrink. -/
set_option linter.hashCommand false
open CategoryTheory AlgebraicGeometry RelativeProjectiveLine
universe u
variable (R : Type u) [CommRing R]
variable (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme]
example (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)
    (s : Spec (.of R)) :
    ∃ r : R, s ∈ PrimeSpectrum.basicOpen r ∧ Nonempty ((n : ℕ) →
      ((Scheme.Modules.pullback (neighborhoodGraphBoundaryMap R V hV)).obj
        (neighborhoodSerreTwist R V n)).restrict (neighborhoodGraphBoundaryOpen R V hV r).ι ≅
          SheafOfModules.unit (neighborhoodGraphBoundaryOpen R V hV r).toScheme.ringCatSheaf) :=
  exists_neighborhoodGraphRelativeBoundaryTwists R V hV s
#print axioms exists_neighborhoodGraphRelativeBoundaryTwists
#print axioms neighborhoodGraphRelativeBoundaryTwistIso
