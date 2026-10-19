module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Sections.TensorSectionEvaluation
/-! # Original pulled products depend only on the native tensor section -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Scheme.Modules Scheme.Modules.Invertible
universe u

example {X W : Scheme.{u}} (f : W ⟶ X) (L M : LineBundle X)
    (a a' : SheafOfModules.unit X.ringCatSheaf ⟶ L.val)
    (b b' : SheafOfModules.unit X.ringCatSheaf ⟶ M.val)
    (h : (tensorSheafLeftUnit W (SheafOfModules.unit W.ringCatSheaf)).inv ≫
      tensorSheafMap W (pullbackSectionMap f a) (pullbackSectionMap f b) =
      (tensorSheafLeftUnit W (SheafOfModules.unit W.ringCatSheaf)).inv ≫
      tensorSheafMap W (pullbackSectionMap f a') (pullbackSectionMap f b')) :
    Hom.productSection (Hom.pullbackToUnit (sectionDualFunctional X L a) f)
        (Hom.pullbackToUnit (sectionDualFunctional X M b) f) =
      Hom.productSection (Hom.pullbackToUnit (sectionDualFunctional X L a') f)
        (Hom.pullbackToUnit (sectionDualFunctional X M b') f) :=
  tensorSection_eq_product_pulledSectionDualFunctional f L M a b a' b' h

example {X W : Scheme.{u}} (f : W ⟶ X) (I T S : LineBundle X)
    (φ : I.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    (a : SheafOfModules.unit X.ringCatSheaf ⟶
      (tensorLineBundle X T (dualLineBundle X I)).val)
    (n d : SheafOfModules.unit X.ringCatSheaf ⟶ S.val)
    (b : SheafOfModules.unit X.ringCatSheaf ⟶ T.val)
    (h : tensorSectionMap W (pullbackSectionMap f a) (pullbackSectionMap f n) =
      tensorSectionMap W (pullbackSectionMap f (twistedIdealSection X I T φ b))
        (pullbackSectionMap f d)) :
    Hom.productSection
        (Hom.pullbackToUnit (sectionDualFunctional X
          (tensorLineBundle X T (dualLineBundle X I)) a) f)
        (Hom.pullbackToUnit (sectionDualFunctional X S n) f) =
      Hom.productSection
        (Hom.pullbackToUnit (sectionDualFunctional X
          (tensorLineBundle X T (dualLineBundle X I)) (twistedIdealSection X I T φ b)) f)
        (Hom.pullbackToUnit (sectionDualFunctional X S d) f) :=
  tensorSection_eq_product_pulledSectionDualFunctional f
    (tensorLineBundle X T (dualLineBundle X I)) S a n (twistedIdealSection X I T φ b) d h

open Lean in
run_cmd do
  for name in #[``tensorSectionPairing_tmul, ``pairedSectionFunctional_tensorSectionMap,
      ``tensorSection_eq_product_pairedSectionFunctional,
      ``tensorSection_eq_product_pulledSectionDualFunctional] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original pulled functional products use only standard foundations."
