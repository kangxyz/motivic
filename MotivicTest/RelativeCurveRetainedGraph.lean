module
import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Common.RetainedGraphIdeal
import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Common.RetainedSourceChange
/-! # The literal retained graph and original ideal comparison -/
set_option linter.hashCommand false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil
variable {S C Y B V : Scheme.{u}} (π : C ⟶ S) [IsSeparated π]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
  (α : B ⟶ Y) [Flat α] (v : V ⟶ C) [IsOpenImmersion v]
  (φ : B ⟶ V) (hφ : φ ≫ v = α ≫ j)
example :
    (relativeRetainedGraphIdealIso π j α v φ hφ).hom ≫
      Hom.idealInclusion (relativeRetainedGraph π j α v φ hφ) =
    Modules.Hom.pullbackToUnit (Hom.idealInclusion (Hom.compactificationGraph π j))
      (retainedProductInclusion (commonProjection π j α) π v ≫ commonToLambda π j α) :=
  relativeRetainedGraphIdealIso_inclusion π j α v φ hφ
#print axioms relativeRetainedGraphIdealIso_inclusion
#print axioms retainedToLambda_isPullback
#print axioms retainedToPsi_isPullback
end AlgebraicGeometry.Scheme.RelativeCurvePencil
