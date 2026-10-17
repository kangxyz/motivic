module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.NeighborhoodNormalizedBoundary
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.NeighborhoodLocalGraphFunctional
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.NeighborhoodBoundaryCoordinate
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.OpenBoundaryCoordinatePullback
/-! # The actual local graph coordinate is the original boundary coordinate pulled back -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R]
variable (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme]
variable (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)
variable (r : R)

/-- Native local dualization and the original graph boundary frame preserve the scalar. -/
theorem neighborhoodLocalBoundaryFrame_coordinate :
    pullbackSectionMap
        (neighborhoodGraphBoundaryMap R V hV ∣_ neighborhoodSectionOpen R V r)
        (canonicalDualHom _ (neighborhoodLocalIdeal R V r).val
          (neighborhoodLocalGraphFunctional R V r)) ≫
        (neighborhoodLocalBoundaryFrame R V hV r).hom =
      Scheme.Hom.unitEndomorphismPullback
        ((neighborhoodGraphBoundaryMap R V hV) ⁻¹ᵁ neighborhoodSectionOpen R V r).ι
        (neighborhoodBoundaryCoordinate R V hV) :=
  openDualBoundaryFrame_coordinate (neighborhoodGraphBoundaryMap R V hV)
    (neighborhoodSectionOpen R V r) (neighborhoodGraphLine R V)
    (Scheme.Hom.idealInclusion (Scheme.Hom.compactificationGraph
      (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) (neighborhoodInclusion R V)))
    (neighborhoodGraphBoundaryIso R V hV)

end AlgebraicGeometry.RelativeProjectiveLine
