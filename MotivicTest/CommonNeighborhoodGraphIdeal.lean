module
import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.CommonNeighborhoodGraphIdeal
/-! The original common graph ideal and its original canonical section are retained. -/
set_option linter.hashCommand false
open CategoryTheory AlgebraicGeometry RelativeProjectiveLine
universe u
variable (R : Type u) [CommRing R]
  (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme] (r : R)
example : IsClosedImmersion (commonNeighborhoodGraph R V r) := inferInstance
example : (commonNeighborhoodLocalGraphIdealIso R V r).hom ≫
    Scheme.Hom.idealInclusion (commonNeighborhoodGraph R V r) =
    Scheme.Modules.Hom.pullbackToUnit (neighborhoodLocalGraphFunctional R V r)
      (commonNeighborhoodToSectionAmbient R V r) :=
  commonNeighborhoodLocalGraphIdealIso_inclusion R V r
#print axioms commonNeighborhoodGraph_isPullback
#print axioms commonNeighborhoodLocalGraphIdealIso_inclusion
