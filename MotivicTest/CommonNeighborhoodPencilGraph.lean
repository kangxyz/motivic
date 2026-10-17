module
import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.CommonNeighborhoodPencilGraph
/-! The actual global graph section is the literal compact zero endpoint. -/
set_option linter.hashCommand false
open CategoryTheory AlgebraicGeometry RelativeProjectiveLine
open Scheme.Modules Scheme.Modules.Invertible
universe u
variable (R : Type u) [CommRing R]
  (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme] (r : R)
  (T : LineBundle (neighborhoodSectionOpen R V r).toScheme)
  (N : LineBundle (fixedPsiAmbient R r))
example
    (b : SheafOfModules.unit (neighborhoodSectionOpen R V r).toScheme.ringCatSheaf ⟶ T.val)
    (d : SheafOfModules.unit (fixedPsiAmbient R r).ringCatSheaf ⟶ N.val) :
    (commonNeighborhoodGraphPencilIso R V r T N).hom ≫
      Scheme.Modules.Hom.productSection
        (Scheme.Modules.Hom.pullbackToUnit
          (sectionDualFunctional _ (tensorLineBundle _ T
            (dualLineBundle _ (neighborhoodLocalIdeal R V r)))
            (twistedIdealSection _ (neighborhoodLocalIdeal R V r) T
              (neighborhoodLocalGraphFunctional R V r) b))
          (commonNeighborhoodToSectionAmbient R V r))
        (Scheme.Modules.Hom.pullbackToUnit (sectionDualFunctional _ N d)
          (commonNeighborhoodToPsiAmbient R V r)) =
    Scheme.Modules.Hom.productSection (Scheme.Hom.idealInclusion (commonNeighborhoodGraph R V r))
      (Scheme.Modules.Hom.productSection
        (Scheme.Modules.Hom.pullbackToUnit (sectionDualFunctional _ T b)
          (commonNeighborhoodToSectionAmbient R V r))
        (Scheme.Modules.Hom.pullbackToUnit (sectionDualFunctional _ N d)
          (commonNeighborhoodToPsiAmbient R V r))) :=
  commonNeighborhoodGraphPencilIso_start R V r T N b d
#print axioms commonNeighborhoodGraphPencilIso_start
#print axioms commonNeighborhoodGraph_rankOne
