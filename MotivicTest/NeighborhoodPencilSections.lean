module
import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.NeighborhoodPencilSections
/-! Actual section data are constructed near the original base point, without section inputs. -/
set_option linter.hashCommand false
open CategoryTheory AlgebraicGeometry RelativeProjectiveLine
universe u
variable (R : Type u) [CommRing R] [IsNoetherianRing R]
  (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme]
  (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)
example (s : Spec (.of R)) :
    ∃ r : R, s ∈ PrimeSpectrum.basicOpen r ∧ Nonempty (NeighborhoodPencilSections R V hV r) :=
  exists_neighborhoodPencilSections R V hV s
#print axioms exists_neighborhoodPencilSections
