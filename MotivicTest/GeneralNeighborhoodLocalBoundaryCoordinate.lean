module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Graph.LocalBoundaryCoordinate
import Lean.Util.CollectAxioms
/-! # Direct concrete original-coordinate consumer -/
public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open RelativeProjectiveLine Scheme.Modules Scheme.Modules.Invertible
universe u
namespace MotivicTest.LocalBoundaryCoordinate
variable (R : Type u) [CommRing R]
variable (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme]
variable (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)
variable (r : R)

/-- Native local dualization and the original graph boundary frame preserve the scalar. -/
theorem actual_local_coordinate :
    pullbackSectionMap
        (neighborhoodGraphBoundaryMap R V hV ∣_ neighborhoodSectionOpen R V r)
        (canonicalDualHom _ (neighborhoodLocalIdeal R V r).val
          (neighborhoodLocalGraphFunctional R V r)) ≫
        (neighborhoodLocalBoundaryFrame R V hV r).hom =
      Scheme.Hom.unitEndomorphismPullback
        ((neighborhoodGraphBoundaryMap R V hV) ⁻¹ᵁ neighborhoodSectionOpen R V r).ι
        (neighborhoodBoundaryCoordinate R V hV) :=
  neighborhoodLocalBoundaryFrame_coordinate R V hV r

end MotivicTest.LocalBoundaryCoordinate
open Lean in
run_cmd do
  for dependency in ← collectAxioms `MotivicTest.LocalBoundaryCoordinate.actual_local_coordinate do
    unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
      throwError "Original coordinate depends on unsupported assumption {dependency}"
  logInfo "Concrete original local graph coordinate: standard axioms only."
