module
import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.ZeroNeighborhoodBoundary
/-! Direct original-neighborhood and nonreduced-boundary consumers. -/
set_option linter.hashCommand false
open CategoryTheory AlgebraicGeometry RelativeProjectiveLine
universe u
variable (R : Type u) [CommRing R]

example (V : (Spec (.of (Polynomial R))).Opens)
    (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V) :
    IsClosedImmersion (fullNeighborhoodBoundaryMap R V) ∧
      IsFinite (fullNeighborhoodBoundaryMap R V ≫
        ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) :=
  ⟨fullNeighborhoodBoundary_closed R V hV, fullNeighborhoodBoundary_finite R V hV⟩

example {B : Scheme.{u}} (i : B ⟶ ProjectiveSpace R (ULift.{u} (Fin 2)))
    [IsClosedImmersion i] (h : Disjoint (Set.range i) (Set.range (zeroSection R))) :
    IsFinite (i ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) :=
  isFinite_boundary_disjoint_zero R i h

example : Set.range (zeroSection R) =
    (ProjectiveSpace.coordinateOpen R (ULift.{u} (Fin 2)) ⟨1⟩ : Set _)ᶜ :=
  range_zeroSection R

#print axioms fullNeighborhoodBoundary_finite
#print axioms fullNeighborhoodBoundary_closed
#print axioms range_zeroSection
