module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Refinement.SectionBoundary
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Refinement.ProductUnit
/-! # Literal compact pencil equality from the actual two relative section producers -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R]
  (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme]
  (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)
  (r : R) (l m : ℕ) (e : neighborhoodFrame R V r l)

theorem NeighborhoodSectionPair.common_pencil_boundary
    (d : NeighborhoodSectionPair R V hV r l e)
    (n t : SheafOfModules.unit (fixedPsiAmbient R r).ringCatSheaf ⟶
      (fixedPsiTwistLine R r m).val)
    (hn : pullbackSectionMap (fixedPsiBoundaryMap R r V) n =
      (fixedPsiBoundaryUnit R V r).hom ≫ pullbackSectionMap (fixedPsiBoundaryMap R r V) t) :
    Scheme.Modules.Hom.pullbackToUnit
      (mixedProductFunctional (commonNeighborhoodToSectionAmbient R V r)
        (commonNeighborhoodToPsiAmbient R V r)
        (tensorLineBundle _ (neighborhoodLocalTwist R V r l)
          (dualLineBundle _ (neighborhoodLocalIdeal R V r)))
        (fixedPsiTwistLine R r m) d.normalizedNumerator n)
      (commonNeighborhoodBoundaryMap R V r) =
    Scheme.Modules.Hom.pullbackToUnit
      (mixedProductFunctional (commonNeighborhoodToSectionAmbient R V r)
        (commonNeighborhoodToPsiAmbient R V r)
        (tensorLineBundle _ (neighborhoodLocalTwist R V r l)
          (dualLineBundle _ (neighborhoodLocalIdeal R V r)))
        (fixedPsiTwistLine R r m)
        (twistedIdealSection _ (neighborhoodLocalIdeal R V r)
          (neighborhoodLocalTwist R V r l) (neighborhoodLocalGraphFunctional R V r)
          d.normalizedDenominator) t)
      (commonNeighborhoodBoundaryMap R V r) := by
  apply mixedProductFunctional_boundary
  rw [← commonNeighborhoodBoundaryToSection_fac R V r hV,
    ← commonNeighborhoodBoundaryToPsi_fac R V r]
  exact d.common_boundary_tensor R V hV r l m e n t hn
end AlgebraicGeometry.RelativeProjectiveLine
