module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.DualTensor.Pullback
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Sections.TensorSectionEvaluation
/-! # The full boundary tensor equality retains the original global line comparison -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- Equality of the actual two-factor boundary sections gives the original signed-pencil
functional equality through the pullback of the original global line isomorphism. -/
theorem dualTwistedIdealProductIso_boundary {X W : Scheme.{u}} (f : W ⟶ X)
    (I T S : LineBundle X) (φ : I.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    (b : SheafOfModules.unit X.ringCatSheaf ⟶ T.val)
    (d n : SheafOfModules.unit X.ringCatSheaf ⟶ S.val)
    (a : SheafOfModules.unit X.ringCatSheaf ⟶
      (tensorLineBundle X T (dualLineBundle X I)).val)
    (h : (tensorSheafLeftUnit W (SheafOfModules.unit W.ringCatSheaf)).inv ≫
        tensorSheafMap W (pullbackSectionMap f a) (pullbackSectionMap f n) =
      (tensorSheafLeftUnit W (SheafOfModules.unit W.ringCatSheaf)).inv ≫
        tensorSheafMap W (pullbackSectionMap f (twistedIdealSection X I T φ b))
          (pullbackSectionMap f d)) :
    (Modules.pullback f).map (dualTwistedIdealProductIso X I T S).hom ≫
      pullbackTensorMap f
        (dualLineBundle X (tensorLineBundle X T (dualLineBundle X I))).val
        (dualLineBundle X S).val ≫
      Hom.productSection
        (Hom.pullbackToUnit
          (sectionDualFunctional X (tensorLineBundle X T (dualLineBundle X I)) a) f)
        (Hom.pullbackToUnit (sectionDualFunctional X S n) f) =
    Hom.pullbackToUnit
      (Hom.productSection φ (Hom.productSection (sectionDualFunctional X T b)
        (sectionDualFunctional X S d))) f := by
  rw [tensorSection_eq_product_pulledSectionDualFunctional f
    (tensorLineBundle X T (dualLineBundle X I)) S a n (twistedIdealSection X I T φ b) d h]
  exact dualTwistedIdealProductIso_pullback_section f I T S φ b d
/-- The same exact boundary equality in the native pulled-factor tensor domain. -/
theorem pulledDualTwistedIdealProductIso_boundary {X W : Scheme.{u}} (f : W ⟶ X)
    (I T S : LineBundle X) (φ : I.val ⟶ SheafOfModules.unit X.ringCatSheaf)
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
        (Hom.pullbackToUnit (sectionDualFunctional X S d) f)) := by
  rw [tensorSection_eq_product_pulledSectionDualFunctional f
    (tensorLineBundle X T (dualLineBundle X I)) S a n (twistedIdealSection X I T φ b) d h]
  exact pulledDualTwistedIdealProductIso_section f I T S φ b d
end AlgebraicGeometry.Scheme.Modules.Invertible
