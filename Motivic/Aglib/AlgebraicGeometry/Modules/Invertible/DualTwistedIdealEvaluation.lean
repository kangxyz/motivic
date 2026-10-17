module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.DualTwistedIdeal
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.TensorLineBundleSections
public import Motivic.Aglib.AlgebraicGeometry.ProductSectionIdeals
/-! # Original section compatibility for the dual twisted ideal -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct
universe u
namespace AlgebraicGeometry.Scheme.Modules.Invertible

theorem twistedIdealPairingIso_hom_tmul (X : Scheme.{u}) (I T : LineBundle X)
    (U : X.Opensᵒᵖ) (i : I.val.val.obj U) (d : (dualLineBundle X T).val.val.obj U)
    (t : T.val.val.obj U) (e : (dualLineBundle X I).val.val.obj U) :
    (twistedIdealPairingIso X I T).hom.val.app U
      ((tensorSheafUnit X (tensorSheaf X I.val (dualLineBundle X T).val)
        (tensorSheaf X T.val (dualLineBundle X I).val)).app U
        ((tensorSheafUnit X I.val (dualLineBundle X T).val).app U (i ⊗ₜ d) ⊗ₜ
          (tensorSheafUnit X T.val (dualLineBundle X I).val).app U (t ⊗ₜ e))) =
    (show X.presheaf.obj U from d.val.app (op (Over.mk (𝟙 U.unop))) t) *
      (show X.presheaf.obj U from e.val.app (op (Over.mk (𝟙 U.unop))) i) := by
  have h1 := tensorLineBundleAssociator_hom_tmul X I (dualLineBundle X T)
    (tensorLineBundle X T (dualLineBundle X I)) U i d
    ((tensorSheafUnit X T.val (dualLineBundle X I).val).app U (t ⊗ₜ e))
  have h2 := tensorLineBundleAssociator_inv_tmul X (dualLineBundle X T) T
    (dualLineBundle X I) U d t e
  dsimp only [twistedIdealPairingIso, Iso.trans_hom, Iso.symm_hom]
  change (dualEvaluationIso X I).hom.val.app U
    ((tensorSheafBraiding X I.val (dualLineBundle X I).val).hom.val.app U
      ((tensorSheafMap X (𝟙 I.val) (tensorSheafLeftUnit X (dualLineBundle X I).val).hom).val.app U
        ((tensorSheafMap X (𝟙 I.val)
          (tensorSheafMap X (dualEvaluationIso X T).hom (𝟙 (dualLineBundle X I).val))).val.app U
          ((tensorSheafMap X (𝟙 I.val)
            (tensorLineBundleAssociator X (dualLineBundle X T) T
              (dualLineBundle X I)).inv).val.app U
            ((tensorLineBundleAssociator X I (dualLineBundle X T)
              (tensorLineBundle X T (dualLineBundle X I))).hom.val.app U _))))) = _
  dsimp only [tensorLineBundle] at h1
  erw [h1]
  rw [tensorSheafMap_tmul, h2, tensorSheafMap_tmul, tensorSheafMap_tmul,
    tensorSheafMap_tmul, dualEvaluationIso_hom_tmul, tensorSheafLeftUnit_tmul,
    tensorSheafBraiding_hom_tmul, dualEvaluationIso_hom_tmul]
  change X.presheaf.map (𝟙 U.unop).op _ * _ = _
  simp
  rfl

/-- The inverse right unit inserts the literal unit section. -/
theorem tensorSheafRightUnit_inv_apply (X : Scheme.{u}) (M : X.Modules)
    (U : X.Opensᵒᵖ) (m : M.val.obj U) :
    (tensorSheafRightUnit X M).inv.val.app U m =
      (tensorSheafUnit X M (SheafOfModules.unit X.ringCatSheaf)).app U
        (m ⊗ₜ (1 : X.presheaf.obj U)) := by
  have h := tensorSheafRightUnit_tmul X M U m 1
  rw [one_smul] at h
  conv_lhs => rw [← h]
  exact congrArg (fun k => k.val.app U
    ((tensorSheafUnit X M (SheafOfModules.unit X.ringCatSheaf)).app U
      (m ⊗ₜ (1 : X.presheaf.obj U))))
    (tensorSheafRightUnit X M).hom_inv_id

/-- The original section functional is literal evaluation at the original section value. -/
theorem sectionDualFunctional_apply (X : Scheme.{u}) (T : LineBundle X)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ T.val) (U : X.Opensᵒᵖ)
    (d : (dualLineBundle X T).val.val.obj U) :
    (sectionDualFunctional X T s).val.app U d =
      d.val.app (op (Over.mk (𝟙 U.unop))) (s.val.app U (1 : X.presheaf.obj U)) := by
  change (dualEvaluationIso X T).hom.val.app U
    ((tensorSheafMap X (𝟙 _) s).val.app U ((tensorSheafRightUnit X _).inv.val.app U d)) = _
  rw [tensorSheafRightUnit_inv_apply, tensorSheafMap_tmul, dualEvaluationIso_hom_tmul]
  rfl

/-- The original tensor of a supplied section with the canonical dual divisor section. -/
def twistedIdealSection (X : Scheme.{u}) (I T : LineBundle X)
    (φ : I.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ T.val) :
    SheafOfModules.unit X.ringCatSheaf ⟶ (tensorLineBundle X T (dualLineBundle X I)).val :=
  (tensorSheafLeftUnit X (SheafOfModules.unit X.ringCatSheaf)).inv ≫
    tensorSheafMap X s (canonicalDualHom X I.val φ)

theorem tensorSheafLeftUnit_inv_apply (X : Scheme.{u}) (M : X.Modules)
    (U : X.Opensᵒᵖ) (m : M.val.obj U) :
    (tensorSheafLeftUnit X M).inv.val.app U m =
      (tensorSheafUnit X (SheafOfModules.unit X.ringCatSheaf) M).app U
        ((1 : X.presheaf.obj U) ⊗ₜ m) := by
  have h := tensorSheafLeftUnit_tmul X M U 1 m
  rw [one_smul] at h
  conv_lhs => rw [← h]
  exact congrArg (fun k => k.val.app U
    ((tensorSheafUnit X (SheafOfModules.unit X.ringCatSheaf) M).app U
      ((1 : X.presheaf.obj U) ⊗ₜ m))) (tensorSheafLeftUnit X M).hom_inv_id

theorem twistedIdealSection_apply_one (X : Scheme.{u}) (I T : LineBundle X)
    (φ : I.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ T.val) (U : X.Opensᵒᵖ) :
    (twistedIdealSection X I T φ s).val.app U (1 : X.presheaf.obj U) =
    (tensorSheafUnit X T.val (dualLineBundle X I).val).app U
      (s.val.app U (1 : X.presheaf.obj U) ⊗ₜ
        (canonicalDualHom X I.val φ).val.app U (1 : X.presheaf.obj U)) := by
  change (tensorSheafMap X s (canonicalDualHom X I.val φ)).val.app U
    ((tensorSheafLeftUnit X _).inv.val.app U (1 : X.presheaf.obj U)) = _
  rw [tensorSheafLeftUnit_inv_apply, tensorSheafMap_tmul]
  rfl

theorem canonicalDualHom_apply_one_evaluation (X : Scheme.{u}) (I : LineBundle X)
    (φ : I.val ⟶ SheafOfModules.unit X.ringCatSheaf) (U : X.Opensᵒᵖ)
    (i : I.val.val.obj U) :
    ((canonicalDualHom X I.val φ).val.app U (1 : X.presheaf.obj U)).val.app
      (op (Over.mk (𝟙 U.unop))) i = φ.val.app U i := by
  have h := congrArg (fun k => k.val.app U
    ((tensorSheafUnit X (SheafOfModules.unit X.ringCatSheaf) I.val).app U
      ((1 : X.presheaf.obj U) ⊗ₜ i))) (canonicalDualHom_evaluation X I.val φ)
  change (evaluationSheaf X I.val (SheafOfModules.unit X.ringCatSheaf)).val.app U
    ((tensorSheafMap X (canonicalDualHom X I.val φ) (𝟙 I.val)).val.app U _) =
    φ.val.app U ((tensorSheafLeftUnit X I.val).hom.val.app U _) at h
  rw [← dualEvaluationIso_hom X I, tensorSheafMap_tmul] at h
  erw [dualEvaluationIso_hom_tmul X I U, tensorSheafLeftUnit_tmul, one_smul] at h
  exact h

/-- Inserting the original tensor section in the original pairing gives the literal product. -/
theorem twistedIdealPairingIso_section (X : Scheme.{u}) (I T : LineBundle X)
    (φ : I.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ T.val) :
    (tensorSheafRightUnit X (tensorLineBundle X I (dualLineBundle X T)).val).inv ≫
      tensorSheafMap X (𝟙 _) (twistedIdealSection X I T φ s) ≫
      (twistedIdealPairingIso X I T).hom =
    Hom.productSection φ (sectionDualFunctional X T s) := by
  apply (_root_.PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)).injective
  ext U : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro i d
  change I.val.val.obj U at i
  change (dualLineBundle X T).val.val.obj U at d
  change (twistedIdealPairingIso X I T).hom.val.app U
    ((tensorSheafMap X (𝟙 _) (twistedIdealSection X I T φ s)).val.app U
      ((tensorSheafRightUnit X _).inv.val.app U
        ((tensorSheafUnit X I.val (dualLineBundle X T).val).app U (i ⊗ₜ d)))) =
    (Hom.productSection φ (sectionDualFunctional X T s)).val.app U
      ((tensorSheafUnit X I.val (dualLineBundle X T).val).app U (i ⊗ₜ d))
  rw [tensorSheafRightUnit_inv_apply, tensorSheafMap_tmul, twistedIdealSection_apply_one]
  change (twistedIdealPairingIso X I T).hom.val.app U
    ((tensorSheafUnit X (tensorSheaf X I.val (dualLineBundle X T).val)
      (tensorSheaf X T.val (dualLineBundle X I).val)).app U
      ((tensorSheafUnit X I.val (dualLineBundle X T).val).app U (i ⊗ₜ d) ⊗ₜ
        (tensorSheafUnit X T.val (dualLineBundle X I).val).app U
          (s.val.app U (1 : X.presheaf.obj U) ⊗ₜ
            (canonicalDualHom X I.val φ).val.app U (1 : X.presheaf.obj U)))) = _
  rw [twistedIdealPairingIso_hom_tmul, canonicalDualHom_apply_one_evaluation]
  have hp := Hom.productSection_tensor φ (sectionDualFunctional X T s) U.unop i d
  change (Hom.productSection φ (sectionDualFunctional X T s)).val.app U
      ((tensorSheafUnit X I.val (dualLineBundle X T).val).app U (i ⊗ₜ d)) =
    (show X.presheaf.obj U from φ.val.app U i) *
      (show X.presheaf.obj U from (sectionDualFunctional X T s).val.app U d) at hp
  rw [hp, sectionDualFunctional_apply, mul_comm]

/-- Naturality of evaluating an original section against a supplied dual functional. -/
theorem comp_sectionDualFunctional (X : Scheme.{u}) (N : LineBundle X) (M : X.Modules)
    (f : M ⟶ (dualLineBundle X N).val)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ N.val) :
    f ≫ sectionDualFunctional X N s =
      (tensorSheafRightUnit X M).inv ≫ tensorSheafMap X f s ≫
        (dualEvaluationIso X N).hom := by
  have hn := (SheafOfModulesOfCommRing.tensorRightUnitIso X.sheaf).inv.naturality f
  change f ≫ (tensorSheafRightUnit X (dualLineBundle X N).val).inv =
    (tensorSheafRightUnit X M).inv ≫
      tensorSheafMap X f (𝟙 (SheafOfModules.unit X.ringCatSheaf)) at hn
  unfold sectionDualFunctional
  rw [← Category.assoc f, hn]
  simp only [Category.assoc]
  have hc := tensorSheafMap_comp X f (𝟙 (SheafOfModules.unit X.ringCatSheaf))
    (𝟙 (dualLineBundle X N).val) s
  simp only [Category.comp_id, Category.id_comp] at hc
  rw [← Category.assoc (tensorSheafMap X f _), hc]

/-- A pairing-preserving identification transfers the proved product identity literally. -/
theorem dualTwistedIdeal_section_of_pairing (X : Scheme.{u}) (I T : LineBundle X)
    (e : (tensorLineBundle X I (dualLineBundle X T)).val ⟶
      (dualLineBundle X (tensorLineBundle X T (dualLineBundle X I))).val)
    (he : tensorSheafMap X e (𝟙 _) ≫
        (dualEvaluationIso X (tensorLineBundle X T (dualLineBundle X I))).hom =
      (twistedIdealPairingIso X I T).hom)
    (φ : I.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ T.val) :
    e ≫ sectionDualFunctional X (tensorLineBundle X T (dualLineBundle X I))
      (twistedIdealSection X I T φ s) =
    Hom.productSection φ (sectionDualFunctional X T s) := by
  rw [comp_sectionDualFunctional]
  have hm : tensorSheafMap X e (twistedIdealSection X I T φ s) =
      tensorSheafMap X (𝟙 _) (twistedIdealSection X I T φ s) ≫
        tensorSheafMap X e (𝟙 _) := by
    rw [tensorSheafMap_comp]
    simp only [Category.id_comp, Category.comp_id]
  rw [hm, Category.assoc, he]
  exact twistedIdealPairingIso_section X I T φ s
end AlgebraicGeometry.Scheme.Modules.Invertible
