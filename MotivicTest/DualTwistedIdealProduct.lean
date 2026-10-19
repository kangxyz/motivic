module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.DualTensor.Product
/-! # Original global line comparison and literal section products -/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules Scheme.Modules.Invertible
universe u
example (X : Scheme.{u}) (I T S : LineBundle X)
    (φ : I.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ T.val)
    (b : (dualLineBundle X S).val ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (dualTwistedIdealProductIso X I T S).hom ≫
      Hom.productSection
        (sectionDualFunctional X (tensorLineBundle X T (dualLineBundle X I))
          (twistedIdealSection X I T φ s)) b =
      Hom.productSection φ (Hom.productSection (sectionDualFunctional X T s) b) :=
  dualTwistedIdealProductIso_section X I T S φ s b

open Lean in
run_cmd do
  for name in #[``dualTwistedIdealIso_pairing, ``dualTwistedIdealIso_section,
      ``dualTwistedIdealProductIso_section] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual line comparison and section product laws use only standard foundations."
