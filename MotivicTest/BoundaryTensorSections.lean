module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Boundary.TensorSections
/-! The full-boundary coordinate produces the literal two-factor section equation. -/
@[expose] public noncomputable section
set_option linter.hashCommand false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
example {X : Scheme.{u}} {T P S : X.Modules}
    (E : P ≅ SheafOfModules.unit X.ringCatSheaf)
    (δ : SheafOfModules.unit X.ringCatSheaf ⟶ P)
    (b : SheafOfModules.unit X.ringCatSheaf ⟶ T)
    (d : SheafOfModules.unit X.ringCatSheaf ⟶ S) :=
  tensorUnitSection_prescribed_coordinate E δ b d
#print axioms tensorUnitSection_prescribed_coordinate
