module
import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.NeighborhoodPencilSpanGeometry
/-! Original relative sources and target become actual smooth-site objects. -/
set_option linter.hashCommand false
open CategoryTheory AlgebraicGeometry Motivic RelativeProjectiveLine
universe u
variable (k R : Type u) [Field k] [CommRing R]
  (b : Spec (.of R) ⟶ Spec (.of k)) [Smooth b]
  (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme] (r : R)
example : (neighborhoodPencilAlpha k R b V r).left =
    commonNeighborhoodToSectionSource R V r := rfl
example : (neighborhoodPencilBeta k R b V r).left = commonNeighborhoodToPsi R V r := rfl
example : (neighborhoodPencilGraph k R b V r).left =
    commonNeighborhoodRetainedTargetMap R V r := rfl
example : Smooth (neighborhoodLambdaSourceMap R V r ≫
    (neighborhoodLambdaSite k R b V r).hom) := neighborhoodLambda_total_smooth k R b V r
#print axioms neighborhoodLambda_total_smooth
#print axioms neighborhoodPencilGraph
