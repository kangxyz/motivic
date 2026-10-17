module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.PrescribedPairPullback
/-! Source change preserves the specified frame and coordinate, not merely triviality. -/
@[expose] public noncomputable section
set_option linter.hashCommand false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace AlgebraicGeometry.Scheme.Modules.Invertible
example {X Y W : Scheme.{u}} (f : W ⟶ Y) (g : Y ⟶ X) (T M : X.Modules)
    (E : (Modules.pullback g).obj M ≅ SheafOfModules.unit Y.ringCatSheaf)
    (a : SheafOfModules.unit X.ringCatSheaf ⟶ tensorSheaf X T M)
    (b : SheafOfModules.unit X.ringCatSheaf ⟶ T)
    (ha : pullbackSectionMap g a ≫ pullbackTensorMap g T M =
      tensorUnitSection (pullbackSectionMap g b) E.inv) :=
  prescribed_pair_pullback f g T M E a b ha
#print axioms prescribed_pair_pullback
#print axioms compositeBoundaryFrame_coordinate
#print axioms scalar_pair_pullback
end AlgebraicGeometry.Scheme.Modules.Invertible
