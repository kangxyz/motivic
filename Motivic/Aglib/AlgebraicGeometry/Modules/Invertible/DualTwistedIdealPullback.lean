module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.DualTwistedIdealProduct
public import Motivic.Aglib.AlgebraicGeometry.ProductSectionPullback
/-! # The original global line comparison under actual boundary pullback -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- The original global product line comparison transported through the native tensor maps. -/
def pulledDualTwistedIdealProductIso {X W : Scheme.{u}} (f : W ⟶ X)
    (I T S : LineBundle X) :
    tensorSheaf W ((Modules.pullback f).obj I.val)
      (tensorSheaf W ((Modules.pullback f).obj (dualLineBundle X T).val)
        ((Modules.pullback f).obj (dualLineBundle X S).val)) ≅
      tensorSheaf W
        ((Modules.pullback f).obj
          (dualLineBundle X (tensorLineBundle X T (dualLineBundle X I))).val)
        ((Modules.pullback f).obj (dualLineBundle X S).val) :=
  tensorSheafIso W (Iso.refl _) (PullbackTensor.Local.pullbackLineBundleTensorIso f
      (dualLineBundle X T) (dualLineBundle X S)).symm ≪≫
    (PullbackTensor.Local.pullbackLineBundleTensorIso f I
      (tensorLineBundle X (dualLineBundle X T) (dualLineBundle X S))).symm ≪≫
    (Modules.pullback f).mapIso (dualTwistedIdealProductIso X I T S) ≪≫
    PullbackTensor.Local.pullbackLineBundleTensorIso f
      (dualLineBundle X (tensorLineBundle X T (dualLineBundle X I))) (dualLineBundle X S)

/-- Pullback retains the original global comparison, not a rebuilt boundary line isomorphism. -/
theorem dualTwistedIdealProductIso_pullback_section {X W : Scheme.{u}} (f : W ⟶ X)
    (I T S : LineBundle X) (φ : I.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    (b : SheafOfModules.unit X.ringCatSheaf ⟶ T.val)
    (d : SheafOfModules.unit X.ringCatSheaf ⟶ S.val) :
    (Modules.pullback f).map (dualTwistedIdealProductIso X I T S).hom ≫
      pullbackTensorMap f
        (dualLineBundle X (tensorLineBundle X T (dualLineBundle X I))).val
        (dualLineBundle X S).val ≫
      Hom.productSection
        (Hom.pullbackToUnit
          (sectionDualFunctional X (tensorLineBundle X T (dualLineBundle X I))
            (twistedIdealSection X I T φ b)) f)
        (Hom.pullbackToUnit (sectionDualFunctional X S d) f) =
    Hom.pullbackToUnit
      (Hom.productSection φ (Hom.productSection (sectionDualFunctional X T b)
        (sectionDualFunctional X S d))) f := by
  rw [← Hom.pullbackToUnit_productSection]
  change (Modules.pullback f).map (dualTwistedIdealProductIso X I T S).hom ≫
    (Modules.pullback f).map _ ≫ (pullbackUnitIso f).hom = _
  rw [← Functor.map_comp_assoc, dualTwistedIdealProductIso_section]
  rfl
/-- In native pulled tensor domains, evaluation still uses the original global comparison. -/
theorem pulledDualTwistedIdealProductIso_section {X W : Scheme.{u}} (f : W ⟶ X)
    (I T S : LineBundle X) (φ : I.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    (b : SheafOfModules.unit X.ringCatSheaf ⟶ T.val)
    (d : SheafOfModules.unit X.ringCatSheaf ⟶ S.val) :
    (pulledDualTwistedIdealProductIso f I T S).hom ≫
      Hom.productSection
        (Hom.pullbackToUnit
          (sectionDualFunctional X (tensorLineBundle X T (dualLineBundle X I))
            (twistedIdealSection X I T φ b)) f)
        (Hom.pullbackToUnit (sectionDualFunctional X S d) f) =
      Hom.productSection (Hom.pullbackToUnit φ f)
        (Hom.productSection (Hom.pullbackToUnit (sectionDualFunctional X T b) f)
          (Hom.pullbackToUnit (sectionDualFunctional X S d) f)) := by
  let A := PullbackTensor.Local.pullbackLineBundleTensorIso f I
    (tensorLineBundle X (dualLineBundle X T) (dualLineBundle X S))
  let B := PullbackTensor.Local.pullbackLineBundleTensorIso f (dualLineBundle X T)
    (dualLineBundle X S)
  simp only [pulledDualTwistedIdealProductIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc]
  change tensorSheafMap W (𝟙 _) B.inv ≫ A.inv ≫
    (Modules.pullback f).map (dualTwistedIdealProductIso X I T S).hom ≫
    pullbackTensorMap f _ _ ≫ _ = _
  rw [dualTwistedIdealProductIso_pullback_section]
  rw [Hom.pullbackToUnit_productSection_lineBundle f I
    (tensorLineBundle X (dualLineBundle X T) (dualLineBundle X S))]
  change tensorSheafMap W (𝟙 _) B.inv ≫ A.inv ≫ A.hom ≫ _ = _
  rw [Iso.inv_hom_id_assoc, Hom.productSection_naturality, Category.id_comp]
  rw [Hom.pullbackToUnit_productSection_lineBundle f (dualLineBundle X T) (dualLineBundle X S)]
  change Hom.productSection _ (B.inv ≫ B.hom ≫ _) = _
  rw [Iso.inv_hom_id_assoc]

end AlgebraicGeometry.Scheme.Modules.Invertible
