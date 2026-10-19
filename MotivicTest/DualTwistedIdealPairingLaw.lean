module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.DualTensor.PairingLaw
/-! # Direct consumer test of original dual twisted ideal evaluation -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible
universe u
example (X : Scheme.{u}) (I T : LineBundle X)
    (φ : I.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ T.val) :
    (dualTwistedIdealIso X I T).hom ≫
      sectionDualFunctional X (tensorLineBundle X T (dualLineBundle X I))
        (twistedIdealSection X I T φ s) =
    Hom.productSection φ (sectionDualFunctional X T s) :=
  dualTwistedIdeal_section_of_pairing X I T (dualTwistedIdealIso X I T).hom
    (dualTwistedIdealIso_pairing X I T) φ s
