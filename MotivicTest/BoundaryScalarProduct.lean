module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Boundary.ScalarProduct
/-! Direct consumer of the literal prescribed-coordinate product. -/
@[expose] public noncomputable section
set_option linter.hashCommand false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
example (X : Scheme.{u}) (I T S : LineBundle X)
    (ε : I.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    (b : SheafOfModules.unit X.ringCatSheaf ⟶ T.val)
    (d : SheafOfModules.unit X.ringCatSheaf ⟶ S.val)
    (c : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :=
  dualTwistedIdealProductIso_coordinate X I T S ε b d c
#print axioms dualTwistedIdealProductIso_coordinate
