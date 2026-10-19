module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Graph.NormalizedBoundary
import Lean.Util.CollectAxioms
/-! # Direct consumer of the actual neighborhood section boundary equation -/
public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open RelativeProjectiveLine Scheme.Modules Scheme.Modules.Invertible
universe u
namespace MotivicTest.NormalizedBoundary

theorem actual_generated_pair (R : Type u) [CommRing R]
    (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme]
    (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)
    (r : R) (n : ℕ) (e : neighborhoodFrame R V r n)
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
      (neighborhoodLocalBoundaryFrame R V hV r).inv :=
  d.normalized_boundary_tensor

/-- The canonical local coordinate is the restriction of the original coordinate. -/
theorem original_coordinate {Z C : Scheme.{u}} (z : Z ⟶ C) (U : C.Opens)
    (I : LineBundle C) (φ : I.val ⟶ SheafOfModules.unit C.ringCatSheaf)
    (E : (Scheme.Modules.pullback z).obj (dualLineBundle C I).val ≅
      SheafOfModules.unit Z.ringCatSheaf) :
    pullbackSectionMap (z ∣_ U)
        (canonicalDualHom U.toScheme (restrictLineBundle U.ι I).val
          ((Scheme.Modules.restrictFunctor U.ι).map φ ≫ (restrictUnitIso U.ι).hom)) ≫
        (openDualBoundaryFrame z U I E).hom =
      (restrictUnitIso (z ⁻¹ᵁ U).ι).inv ≫
        (Scheme.Modules.restrictFunctor (z ⁻¹ᵁ U).ι).map
          (pullbackSectionMap z (canonicalDualHom C I.val φ) ≫ E.hom) ≫
        (restrictUnitIso (z ⁻¹ᵁ U).ι).hom :=
  pullbackSectionMap_openDualBoundaryFrame z U I φ E

end MotivicTest.NormalizedBoundary
open Lean in
run_cmd do
  let targets := #[
    `MotivicTest.NormalizedBoundary.actual_generated_pair,
    `MotivicTest.NormalizedBoundary.original_coordinate,
    `AlgebraicGeometry.Scheme.Modules.Invertible.pullbackSectionMap_openDualBoundaryFrame,
    `AlgebraicGeometry.Scheme.CoherentGraph.open_prescribed_normalized]
  for name in targets do
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual generated normalized pair and original coordinate: standard axioms only."
