module
import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.NeighborhoodOpenSectionPair
/-! The actual constructed numerator and denominator are units on the full boundary. -/
set_option linter.hashCommand false
open CategoryTheory AlgebraicGeometry RelativeProjectiveLine
open Scheme.Modules Scheme.Modules.Invertible
universe u
variable (R : Type u) [CommRing R]
variable (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme]
example (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)
    (r : R) (n : ℕ) (e : neighborhoodFrame R V r n)
    (d : NeighborhoodSectionPair R V hV r n e) :
    IsIso (pullbackSectionMap
      (neighborhoodGraphBoundaryMap R V hV ∣_ neighborhoodSectionOpen R V r) d.numeratorHom) ∧
    IsIso (pullbackSectionMap
      (neighborhoodGraphBoundaryMap R V hV ∣_ neighborhoodSectionOpen R V r) d.denominatorHom) :=
  ⟨d.numeratorHom_boundary_isIso, d.denominatorHom_boundary_isIso⟩
#print axioms exists_neighborhoodSectionPair
#print axioms NeighborhoodSectionPair.numeratorHom_boundary_isIso
#print axioms NeighborhoodSectionPair.denominatorHom_boundary_isIso
