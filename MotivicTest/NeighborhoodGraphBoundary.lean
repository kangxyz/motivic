module
import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Graph.Boundary
/-! Actual graph and prescribed full boundary over an arbitrary ring. -/
set_option linter.hashCommand false
open CategoryTheory AlgebraicGeometry RelativeProjectiveLine
universe u
variable (R : Type u) [CommRing R]
variable (V : (Spec (.of (Polynomial R))).Opens)
variable (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)
example : IsClosedImmersion (neighborhoodGraphBoundaryMap R V hV) :=
  neighborhoodGraphBoundary_closed R V hV
example : IsFinite (neighborhoodGraphBoundaryMap R V hV ≫
    CategoryTheory.Limits.pullback.fst (neighborhoodProjection R V)
      (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))) :=
  neighborhoodGraphBoundary_finite R V hV
example : Nonempty ((Scheme.Modules.pullback (neighborhoodGraphBoundaryMap R V hV)).obj
    (neighborhoodGraphDivisor R V).val ≅
      SheafOfModules.unit (neighborhoodGraphBoundarySource R V hV).ringCatSheaf) :=
  ⟨neighborhoodGraphBoundaryIso R V hV⟩
#print axioms neighborhoodGraphBoundaryIso_missing
#print axioms neighborhoodGraphBoundaryIso_zero
#print axioms neighborhoodGraphBoundary_finite
