module
import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Pencil.FiniteFlatFamily
/-! Genuine finite-flat polynomial families are constructed from original neighborhood geometry. -/
set_option linter.hashCommand false
open CategoryTheory AlgebraicGeometry RelativeProjectiveLine
universe u
variable (R : Type u) [CommRing R] [IsNoetherianRing R]
  (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme]
  (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)
example (s : Spec (.of R)) :
    ∃ r : R, s ∈ PrimeSpectrum.basicOpen r ∧
      ∃ d : NeighborhoodPencilSections R V hV r,
        IsFinite (d.familyProjection R V hV r) ∧ Flat (d.familyProjection R V hV r) :=
  exists_neighborhoodFiniteFlatPencil R V hV s
#print axioms NeighborhoodSectionPair.common_family_finite_flat
#print axioms exists_neighborhoodFiniteFlatPencil
