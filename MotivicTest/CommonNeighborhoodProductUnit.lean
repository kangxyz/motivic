module
import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.CommonNeighborhoodProductUnit
import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.NeighborhoodLocalGraphFunctional
/-! The original compact numerator product is a unit on the whole common boundary. -/
set_option linter.hashCommand false
open CategoryTheory AlgebraicGeometry RelativeProjectiveLine
open Scheme.Modules Scheme.Modules.Invertible
universe u
variable (R : Type u) [CommRing R]
variable (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme]
example (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)
    (r : R) (n m : ℕ) (e : neighborhoodFrame R V r n)
    (d : NeighborhoodSectionPair R V hV r n e)
    (a : SheafOfModules.unit (fixedPsiAmbient R r).ringCatSheaf ⟶ (fixedPsiTwistLine R r m).val)
    [IsIso (pullbackSectionMap (fixedPsiBoundaryMap R r V) a)] :
    IsIso (Scheme.Modules.Hom.pullbackToUnit
      (mixedProductFunctional (commonNeighborhoodToSectionAmbient R V r)
        (commonNeighborhoodToPsiAmbient R V r)
        (tensorLineBundle _ (neighborhoodLocalTwist R V r n)
          (dualLineBundle _ (neighborhoodLocalIdeal R V r)))
        (fixedPsiTwistLine R r m) d.normalizedNumerator a)
      (commonNeighborhoodBoundaryMap R V r)) :=
  d.common_product_unit R V hV r n m e a
#print axioms NeighborhoodSectionPair.common_product_unit
#print axioms neighborhoodLocalGraphFunctional_pullback
