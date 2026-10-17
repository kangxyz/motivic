/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.DualTwistedIdealEvaluation
/-! # Equal tensor sections give equal products of original paired functionals -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct
universe u
namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- The native tensor of two structure-module sections. -/
def tensorSectionMap (X : Scheme.{u}) {L M : X.Modules}
    (a : SheafOfModules.unit X.ringCatSheaf ⟶ L)
    (b : SheafOfModules.unit X.ringCatSheaf ⟶ M) :
    SheafOfModules.unit X.ringCatSheaf ⟶ tensorSheaf X L M :=
  (tensorSheafLeftUnit X (SheafOfModules.unit X.ringCatSheaf)).inv ≫
    tensorSheafMap X a b

/-- Insertion of a section into a supplied actual pairing. -/
def pairedSectionFunctional (X : Scheme.{u}) {D L : X.Modules}
    (p : tensorSheaf X D L ⟶ SheafOfModules.unit X.ringCatSheaf)
    (a : SheafOfModules.unit X.ringCatSheaf ⟶ L) :
    D ⟶ SheafOfModules.unit X.ringCatSheaf :=
  (tensorSheafRightUnit X D).inv ≫ tensorSheafMap X (𝟙 D) a ≫ p

/-- The ordered product of two actual pairings, without identifying either dual. -/
def tensorSectionPairing (X : Scheme.{u}) (D E L M : LineBundle X)
    (p : tensorSheaf X D.val L.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    (q : tensorSheaf X E.val M.val ⟶ SheafOfModules.unit X.ringCatSheaf) :
    tensorSheaf X (tensorSheaf X D.val E.val) (tensorSheaf X L.val M.val) ⟶
      SheafOfModules.unit X.ringCatSheaf :=
  (tensorLineBundleAssociator X D E (tensorLineBundle X L M)).hom ≫
    tensorSheafMap X (𝟙 D.val) (tensorLineBundleAssociator X E L M).inv ≫
    tensorSheafMap X (𝟙 D.val)
      (tensorSheafMap X (tensorSheafBraiding X E.val L.val).hom (𝟙 M.val)) ≫
    tensorSheafMap X (𝟙 D.val) (tensorLineBundleAssociator X L E M).hom ≫
    (tensorLineBundleAssociator X D L (tensorLineBundle X E M)).inv ≫
    Hom.productSection p q

/-- The ordered product pairing evaluates literal pure tensors by multiplication. -/
theorem tensorSectionPairing_tmul (X : Scheme.{u}) (D E L M : LineBundle X)
    (p : tensorSheaf X D.val L.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    (q : tensorSheaf X E.val M.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    (U : X.Opensᵒᵖ) (d : D.val.val.obj U) (e : E.val.val.obj U)
    (l : L.val.val.obj U) (m : M.val.val.obj U) :
    (tensorSectionPairing X D E L M p q).val.app U
      ((tensorSheafUnit X (tensorSheaf X D.val E.val)
        (tensorSheaf X L.val M.val)).app U
        ((tensorSheafUnit X D.val E.val).app U (d ⊗ₜ e) ⊗ₜ
          (tensorSheafUnit X L.val M.val).app U (l ⊗ₜ m))) =
    (show X.presheaf.obj U from p.val.app U
      ((tensorSheafUnit X D.val L.val).app U (d ⊗ₜ l))) *
    (show X.presheaf.obj U from q.val.app U
      ((tensorSheafUnit X E.val M.val).app U (e ⊗ₜ m))) := by
  change (Hom.productSection p q).val.app U
    ((tensorLineBundleAssociator X D L (tensorLineBundle X E M)).inv.val.app U
      ((tensorSheafMap X (𝟙 D.val) (tensorLineBundleAssociator X L E M).hom).val.app U
        ((tensorSheafMap X (𝟙 D.val)
          (tensorSheafMap X (tensorSheafBraiding X E.val L.val).hom (𝟙 M.val))).val.app U
          ((tensorSheafMap X (𝟙 D.val) (tensorLineBundleAssociator X E L M).inv).val.app U
            ((tensorLineBundleAssociator X D E (tensorLineBundle X L M)).hom.val.app U _))))) = _
  have h1 := tensorLineBundleAssociator_hom_tmul X D E (tensorLineBundle X L M)
    U d e ((tensorSheafUnit X L.val M.val).app U (l ⊗ₜ m))
  have h5 := tensorLineBundleAssociator_inv_tmul X D L (tensorLineBundle X E M)
    U d l ((tensorSheafUnit X E.val M.val).app U (e ⊗ₜ m))
  dsimp only [tensorLineBundle] at h1 h5
  erw [h1]
  rw [tensorSheafMap_tmul, tensorLineBundleAssociator_inv_tmul,
    tensorSheafMap_tmul, tensorSheafMap_tmul, tensorSheafMap_tmul,
    tensorSheafBraiding_hom_tmul, tensorLineBundleAssociator_hom_tmul]
  erw [h5]
  exact Hom.productSection_tensor p q U.unop _ _

/-- The native tensor section has the expected value at one. -/
theorem tensorSectionMap_apply_one (X : Scheme.{u}) {L M : X.Modules}
    (a : SheafOfModules.unit X.ringCatSheaf ⟶ L)
    (b : SheafOfModules.unit X.ringCatSheaf ⟶ M) (U : X.Opensᵒᵖ) :
    (tensorSectionMap X a b).val.app U (1 : X.presheaf.obj U) =
    (tensorSheafUnit X L M).app U
      (a.val.app U (1 : X.presheaf.obj U) ⊗ₜ b.val.app U (1 : X.presheaf.obj U)) := by
  change (tensorSheafMap X a b).val.app U
    ((tensorSheafLeftUnit X _).inv.val.app U (1 : X.presheaf.obj U)) = _
  rw [tensorSheafLeftUnit_inv_apply, tensorSheafMap_tmul]

/-- Inserting a section into an actual pairing evaluates its value at one. -/
theorem pairedSectionFunctional_apply (X : Scheme.{u}) {D L : X.Modules}
    (p : tensorSheaf X D L ⟶ SheafOfModules.unit X.ringCatSheaf)
    (a : SheafOfModules.unit X.ringCatSheaf ⟶ L)
    (U : X.Opensᵒᵖ) (d : D.val.obj U) :
    (pairedSectionFunctional X p a).val.app U d =
    p.val.app U ((tensorSheafUnit X D L).app U
      (d ⊗ₜ a.val.app U (1 : X.presheaf.obj U))) := by
  change p.val.app U ((tensorSheafMap X (𝟙 D) a).val.app U
    ((tensorSheafRightUnit X D).inv.val.app U d)) = _
  rw [tensorSheafRightUnit_inv_apply, tensorSheafMap_tmul]
  rfl

/-- Evaluation of a native tensor section is the product of the two actual evaluations. -/
theorem pairedSectionFunctional_tensorSectionMap (X : Scheme.{u}) (D E L M : LineBundle X)
    (p : tensorSheaf X D.val L.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    (q : tensorSheaf X E.val M.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    (a : SheafOfModules.unit X.ringCatSheaf ⟶ L.val)
    (b : SheafOfModules.unit X.ringCatSheaf ⟶ M.val) :
    pairedSectionFunctional X (tensorSectionPairing X D E L M p q) (tensorSectionMap X a b) =
    Hom.productSection (pairedSectionFunctional X p a) (pairedSectionFunctional X q b) := by
  apply moduleTensor_hom_ext
  intro U d e
  change (pairedSectionFunctional X (tensorSectionPairing X D E L M p q)
      (tensorSectionMap X a b)).val.app (op U)
      ((tensorSheafUnit X D.val E.val).app (op U) (d ⊗ₜ e)) = _
  rw [pairedSectionFunctional_apply, tensorSectionMap_apply_one, tensorSectionPairing_tmul]
  rw [← pairedSectionFunctional_apply X p a (op U) d,
    ← pairedSectionFunctional_apply X q b (op U) e]
  exact (Hom.productSection_tensor (pairedSectionFunctional X p a)
    (pairedSectionFunctional X q b) U d e).symm

/-- Equal tensor sections remain equal under any two actual line-bundle pairings. -/
theorem tensorSection_eq_product_pairedSectionFunctional (X : Scheme.{u})
    (D E L M : LineBundle X)
    (p : tensorSheaf X D.val L.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    (q : tensorSheaf X E.val M.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    (a : SheafOfModules.unit X.ringCatSheaf ⟶ L.val)
    (b : SheafOfModules.unit X.ringCatSheaf ⟶ M.val)
    (a' : SheafOfModules.unit X.ringCatSheaf ⟶ L.val)
    (b' : SheafOfModules.unit X.ringCatSheaf ⟶ M.val)
    (h : tensorSectionMap X a b = tensorSectionMap X a' b') :
    Hom.productSection (pairedSectionFunctional X p a) (pairedSectionFunctional X q b) =
    Hom.productSection (pairedSectionFunctional X p a') (pairedSectionFunctional X q b') := by
  rw [← pairedSectionFunctional_tensorSectionMap X D E L M,
    ← pairedSectionFunctional_tensorSectionMap X D E L M, h]

/-- Equal normalized pulled tensor sections give equal products of the original
pulled dual functionals, using the actual pulled evaluation and tensor comparison. -/
theorem tensorSection_eq_product_pulledSectionDualFunctional {X W : Scheme.{u}}
    (f : W ⟶ X) (L M : LineBundle X)
    (a : SheafOfModules.unit X.ringCatSheaf ⟶ L.val)
    (b : SheafOfModules.unit X.ringCatSheaf ⟶ M.val)
    (a' : SheafOfModules.unit X.ringCatSheaf ⟶ L.val)
    (b' : SheafOfModules.unit X.ringCatSheaf ⟶ M.val)
    (h : tensorSectionMap W (pullbackSectionMap f a) (pullbackSectionMap f b) =
      tensorSectionMap W (pullbackSectionMap f a') (pullbackSectionMap f b')) :
    Hom.productSection
      (Hom.pullbackToUnit (sectionDualFunctional X L a) f)
      (Hom.pullbackToUnit (sectionDualFunctional X M b) f) =
    Hom.productSection
      (Hom.pullbackToUnit (sectionDualFunctional X L a') f)
      (Hom.pullbackToUnit (sectionDualFunctional X M b') f) := by
  simp only [sectionDualFunctional_pullback]
  exact tensorSection_eq_product_pairedSectionFunctional W
    (pullbackLineBundle f (dualLineBundle X L)) (pullbackLineBundle f (dualLineBundle X M))
    (pullbackLineBundle f L) (pullbackLineBundle f M)
    ((PullbackTensor.Local.pullbackLineBundleTensorIso f (dualLineBundle X L) L).inv ≫
      (Scheme.Modules.pullback f).map (dualEvaluationIso X L).hom ≫ (pullbackUnitIso f).hom)
    ((PullbackTensor.Local.pullbackLineBundleTensorIso f (dualLineBundle X M) M).inv ≫
      (Scheme.Modules.pullback f).map (dualEvaluationIso X M).hom ≫ (pullbackUnitIso f).hom)
    (pullbackSectionMap f a) (pullbackSectionMap f b)
    (pullbackSectionMap f a') (pullbackSectionMap f b') h

end AlgebraicGeometry.Scheme.Modules.Invertible
