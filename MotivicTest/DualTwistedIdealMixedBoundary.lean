module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.DualTensor.MixedBoundary
/-! # Independent lambda and psi source maps retain the original global line comparison -/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules Scheme.Modules.Invertible
universe u
example {X Y W : Scheme.{u}}
    (f : W ⟶ X) (g : W ⟶ Y) (I T : LineBundle X) (S : LineBundle Y)
    (φ : I.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    (b : SheafOfModules.unit X.ringCatSheaf ⟶ T.val)
    (d n : SheafOfModules.unit Y.ringCatSheaf ⟶ S.val)
    (a : SheafOfModules.unit X.ringCatSheaf ⟶
      (tensorLineBundle X T (dualLineBundle X I)).val)
    (h : tensorSectionMap W (pullbackSectionMap f a) (pullbackSectionMap g n) =
      tensorSectionMap W (pullbackSectionMap f (twistedIdealSection X I T φ b))
        (pullbackSectionMap g d)) :
    (mixedPulledDualTwistedIdealProductIso f g I T S).hom ≫
      Hom.productSection
        (Hom.pullbackToUnit
          (sectionDualFunctional X (tensorLineBundle X T (dualLineBundle X I)) a) f)
        (Hom.pullbackToUnit (sectionDualFunctional Y S n) g) =
    Hom.productSection (Hom.pullbackToUnit φ f)
      (Hom.productSection (Hom.pullbackToUnit (sectionDualFunctional X T b) f)
        (Hom.pullbackToUnit (sectionDualFunctional Y S d) g)) :=
  mixedPulledDualTwistedIdealProductIso_boundary f g I T S φ b d n a h

open Lean in
run_cmd do
  for name in #[``tensorSection_eq_product_mixedPulledSectionDualFunctional,
      ``mixedPulledDualTwistedIdealProductIso,
      ``mixedPulledDualTwistedIdealProductIso_boundary] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Independent source maps and original line comparison: standard foundations only."
