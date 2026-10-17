module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.DualTwistedIdealBoundary
/-! # Original pulled line comparison consumes the exact two-factor boundary section equation -/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules Scheme.Modules.Invertible
universe u
example {X W : Scheme.{u}} (f : W ⟶ X) (I T S : LineBundle X)
    (φ : I.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    (b : SheafOfModules.unit X.ringCatSheaf ⟶ T.val)
    (d n : SheafOfModules.unit X.ringCatSheaf ⟶ S.val)
    (a : SheafOfModules.unit X.ringCatSheaf ⟶
      (tensorLineBundle X T (dualLineBundle X I)).val)
    (h : (tensorSheafLeftUnit W (SheafOfModules.unit W.ringCatSheaf)).inv ≫
        tensorSheafMap W (pullbackSectionMap f a) (pullbackSectionMap f n) =
      (tensorSheafLeftUnit W (SheafOfModules.unit W.ringCatSheaf)).inv ≫
        tensorSheafMap W (pullbackSectionMap f (twistedIdealSection X I T φ b))
          (pullbackSectionMap f d)) :
    (pulledDualTwistedIdealProductIso f I T S).hom ≫
      Hom.productSection
        (Hom.pullbackToUnit
          (sectionDualFunctional X (tensorLineBundle X T (dualLineBundle X I)) a) f)
        (Hom.pullbackToUnit (sectionDualFunctional X S n) f) =
    Hom.productSection (Hom.pullbackToUnit φ f)
      (Hom.productSection (Hom.pullbackToUnit (sectionDualFunctional X T b) f)
        (Hom.pullbackToUnit (sectionDualFunctional X S d) f)) :=
  pulledDualTwistedIdealProductIso_boundary f I T S φ b d n a h

open Lean in
run_cmd do
  for name in #[``pulledDualTwistedIdealProductIso,
      ``pulledDualTwistedIdealProductIso_boundary, ``dualTwistedIdealProductIso_boundary] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original pulled line iso boundary evaluation: standard foundations only."
