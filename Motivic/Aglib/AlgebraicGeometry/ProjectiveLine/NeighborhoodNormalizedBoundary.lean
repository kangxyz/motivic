module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.NeighborhoodNormalizedSectionPair
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.OpenPrescribedNormalization
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.OpenBoundaryCoordinate
/-! # The constructed neighborhood pair retains its literal normalized boundary value -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible Scheme.CoherentGraph
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R]
variable (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme]
variable (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)
variable (r : R)

/-- The original graph boundary frame in the actual restricted ideal dual. -/
def neighborhoodLocalBoundaryFrame :
    (Scheme.Modules.pullback
      (neighborhoodGraphBoundaryMap R V hV ∣_ neighborhoodSectionOpen R V r)).obj
        (dualLineBundle _ (neighborhoodLocalIdeal R V r)).val ≅
      SheafOfModules.unit
        ((neighborhoodGraphBoundaryMap R V hV) ⁻¹ᵁ
          neighborhoodSectionOpen R V r).toScheme.ringCatSheaf :=
  openDualBoundaryFrame (neighborhoodGraphBoundaryMap R V hV) (neighborhoodSectionOpen R V r)
    (neighborhoodGraphLine R V) (neighborhoodGraphBoundaryIso R V hV)

attribute [local instance] neighborhoodGraphBoundary_closed
variable {R V hV r} {n : ℕ} {e : neighborhoodFrame R V r n}

/-- The actual constructed sections satisfy the native tensor boundary equation. -/
theorem NeighborhoodSectionPair.normalized_boundary_tensor
    (d : NeighborhoodSectionPair R V hV r n e) :
    pullbackSectionMap
        (neighborhoodGraphBoundaryMap R V hV ∣_ neighborhoodSectionOpen R V r)
        d.normalizedNumerator ≫
      pullbackTensorMap
        (neighborhoodGraphBoundaryMap R V hV ∣_ neighborhoodSectionOpen R V r)
        (neighborhoodLocalTwist R V r n).val
        (dualLineBundle _ (neighborhoodLocalIdeal R V r)).val =
    tensorUnitSection
      (pullbackSectionMap
        (neighborhoodGraphBoundaryMap R V hV ∣_ neighborhoodSectionOpen R V r)
        d.normalizedDenominator)
      (neighborhoodLocalBoundaryFrame R V hV r).inv := by
  have h := open_prescribed_pair (neighborhoodGraphBoundaryMap R V hV)
    (neighborhoodSectionOpen R V r) (neighborhoodSerreTwist R V n)
    (neighborhoodGraphDivisor R V).val (neighborhoodGraphBoundaryIso R V hV)
    d.numerator d.denominator (neighborhoodBoundaryUnitSection R V hV r n e)
    d.numerator_value d.denominator_value
  exact open_prescribed_normalized (neighborhoodGraphBoundaryMap R V hV)
    (neighborhoodSectionOpen R V r) (neighborhoodSerreTwist R V n)
    (neighborhoodGraphDivisor R V).val
    (restrictDualIso (neighborhoodSectionOpen R V r).ι (neighborhoodGraphLine R V))
    (neighborhoodGraphBoundaryIso R V hV) d.numeratorHom d.denominatorHom h

end AlgebraicGeometry.RelativeProjectiveLine
