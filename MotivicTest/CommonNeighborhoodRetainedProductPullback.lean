module
import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Refinement.Retained.ProductPullback
/-! # Direct consumer of the original retained coefficient product comparison -/
open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
open AlgebraicGeometry.RelativeProjectiveLine

example (R : Type) [CommRing R] (V : (Spec (.of (Polynomial R))).Opens)
    [IsAffine V.toScheme] (r : R)
    (L : LineBundle (neighborhoodSectionOpen R V r).toScheme)
    (M : LineBundle (fixedPsiAmbient R r))
    (a : L.val ⟶ SheafOfModules.unit (neighborhoodSectionOpen R V r).toScheme.ringCatSheaf)
    (b : M.val ⟶ SheafOfModules.unit (fixedPsiAmbient R r).ringCatSheaf) :
    (commonNeighborhoodRetainedProductPullbackIso R V r L M).hom ≫
      Scheme.Modules.Hom.pullbackToUnit
        (Scheme.Modules.Hom.productSection
          (Scheme.Modules.Hom.pullbackToUnit a (commonNeighborhoodToSectionAmbient R V r))
          (Scheme.Modules.Hom.pullbackToUnit b (commonNeighborhoodToPsiAmbient R V r)))
        (commonNeighborhoodRetainedInclusion R V r) =
      Scheme.Modules.Hom.productSection (commonNeighborhoodRetainedLambdaFunctional R V r a)
        (commonNeighborhoodRetainedPsiFunctional R V r b) :=
  commonNeighborhoodRetainedProductPullbackIso_functional R V r L M a b
