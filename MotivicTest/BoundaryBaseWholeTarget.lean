module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.WholeTarget
/-! # The original target, not the smaller parameter open, survives base change -/
set_option linter.hashCommand false
public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Hom
variable {S C D Y : Scheme.{u}} (π : C ⟶ S) (d : D ⟶ C)
  (j : Y ⟶ C) (V : S.Opens)
example [IsFinite (d ≫ π)] :
    IsFinite (boundaryBaseWholeMap π d V ≫ pullback.fst V.ι π) :=
  boundaryBaseWholeMap_finite π d V
example [IsClosedImmersion d] : IsClosedImmersion (boundaryBaseWholeMap π d V) :=
  inferInstance
example (hcover : ∀ x : C, x ∈ Set.range j ∨ x ∈ Set.range d)
    (x : boundaryBaseCompactification π V) :
    x ∈ Set.range (boundaryBaseRetainedTarget π V j) ∨
      x ∈ Set.range (boundaryBaseWholeMap π d V) :=
  boundaryBaseWholeTarget_cover π d V j hcover x
example [SmoothOfRelativeDimension 1 (j ≫ π)] :
    SmoothOfRelativeDimension 1
      (boundaryBaseRetainedTarget π V j ≫ pullback.fst V.ι π) :=
  boundaryBaseRetainedTarget_smooth π V j
#print axioms boundaryBaseWholeMap_finite
#print axioms boundaryBaseWholeMap_closed
#print axioms boundaryBaseWholeTarget_cover
#print axioms boundaryBaseRetainedTarget_smooth
end AlgebraicGeometry.Scheme.Hom
