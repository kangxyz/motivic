module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.RelativeCurve.BoundaryGraphBaseIso
/-! # Canonical base presentation preserves the original graph ideal and functional -/
set_option linter.hashCommand false
public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Hom
variable {S X Z : Scheme.{u}} [IsAffine S] (q : X ⟶ S) (z : Z ⟶ X)
  [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (a : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
    idealModule (boundaryGraphTarget q z))
example : SheafOfModules.unit
    (pullback (q ≫ S.isoSpec.hom) (z ≫ q ≫ S.isoSpec.hom)).ringCatSheaf ≅
    idealModule (boundaryGraphTarget (q ≫ S.isoSpec.hom) z) :=
  boundaryGraphFrame_baseIso q z S.isoSpec a
#print axioms boundaryGraphFrame_baseIso
#print axioms boundaryGraphFrame_baseIso_inclusion
#print axioms boundaryGraphBaseIso_graph
end AlgebraicGeometry.Scheme.Hom
