module
import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.FiniteChartBoundary
/-! Whole, possibly nonreduced closed boundary consumer. -/
set_option linter.hashCommand false
open CategoryTheory AlgebraicGeometry
universe u
example (R : Type u) [CommRing R] {B : Scheme.{u}}
    (i : B ⟶ ProjectiveSpace R (ULift.{u} (Fin 2))) [IsClosedImmersion i]
    (h : Set.range i ⊆ ProjectiveSpace.coordinateOpen R (ULift.{u} (Fin 2)) ⟨1⟩) :
    IsFinite (i ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) :=
  ProjectiveSpace.isFinite_boundary_in_coordinateOpen R _ i _ h
#print axioms ProjectiveSpace.isFinite_boundary_in_coordinateOpen
