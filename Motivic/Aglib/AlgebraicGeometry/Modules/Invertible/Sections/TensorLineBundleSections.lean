/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Sections.DualFunctional
/-! # Original evaluation compatibility for the dual twisted ideal -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct
universe u
namespace AlgebraicGeometry.Scheme.Modules.Invertible

private theorem sheafification_map_unit_apply (X : Scheme.{u})
    {P Q : PresheafOfModulesOfCommRing.{u} X.presheaf} (f : P ⟶ Q)
    (U : X.Opensᵒᵖ) (x : P.obj U) :
    ((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map f).val.app U
      (((_root_.PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).unit.app P).app U x) =
    ((_root_.PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).unit.app Q).app U (f.app U x) := by
  exact (congrArg (fun k => k.app U x)
    ((_root_.PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).unit.naturality f)).symm

/-- The original line-bundle associator on pure tensors. -/
theorem tensorLineBundleAssociator_hom_tmul (X : Scheme.{u}) (L M N : LineBundle X)
    (U : X.Opensᵒᵖ) (l : L.val.val.obj U) (m : M.val.val.obj U) (n : N.val.val.obj U) :
    (tensorLineBundleAssociator X L M N).hom.val.app U
      ((tensorSheafUnit X (tensorSheaf X L.val M.val) N.val).app U
        ((tensorSheafUnit X L.val M.val).app U (l ⊗ₜ m) ⊗ₜ n)) =
    (tensorSheafUnit X L.val (tensorSheaf X M.val N.val)).app U
      (l ⊗ₜ (tensorSheafUnit X M.val N.val).app U (m ⊗ₜ n)) := by
  let P := PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) L.val.val M.val.val
  let Q := PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M.val.val N.val.val
  let f := PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf)
    ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P)
    (𝟙 N.val.val)
  let g := PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf)
    (𝟙 L.val.val)
    ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app Q)
  let ef := sheafificationMapIsoOfLocallyBijective X f
    (tensorUnitWhiskerRight_locallyBijective X L.val M.val N.val L.property M.property)
  have hf := sheafification_map_unit_apply X f U ((l ⊗ₜ m) ⊗ₜ n)
  change ef.hom.val.app U _ =
    (tensorSheafUnit X (tensorSheaf X L.val M.val) N.val).app U
        ((tensorSheafUnit X L.val M.val).app U (l ⊗ₜ m) ⊗ₜ n) at hf
  rw [← hf]
  change (ef.hom ≫ (tensorLineBundleAssociator X L M N).hom).val.app U _ = _
  have he : ef.hom ≫ (tensorLineBundleAssociator X L M N).hom =
    (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (CategoryTheory.MonoidalCategory.associator
        (C := PresheafOfModulesOfCommRing.{u} X.presheaf) L.val.val M.val.val N.val.val).hom ≫
    (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map g := by
    dsimp only [tensorLineBundleAssociator, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    change ef.hom ≫ ef.inv ≫ _ = _
    rw [Iso.hom_inv_id_assoc]
    rfl
  rw [he]
  change _ = _
  rw [← Functor.map_comp]
  exact sheafification_map_unit_apply X
    ((CategoryTheory.MonoidalCategory.associator
      (C := PresheafOfModulesOfCommRing.{u} X.presheaf) L.val.val M.val.val N.val.val).hom ≫ g)
    U ((l ⊗ₜ m) ⊗ₜ n)

/-- The inverse original associator on pure tensors. -/
theorem tensorLineBundleAssociator_inv_tmul (X : Scheme.{u}) (L M N : LineBundle X)
    (U : X.Opensᵒᵖ) (l : L.val.val.obj U) (m : M.val.val.obj U) (n : N.val.val.obj U) :
    (tensorLineBundleAssociator X L M N).inv.val.app U
      ((tensorSheafUnit X L.val (tensorSheaf X M.val N.val)).app U
        (l ⊗ₜ (tensorSheafUnit X M.val N.val).app U (m ⊗ₜ n))) =
    (tensorSheafUnit X (tensorSheaf X L.val M.val) N.val).app U
      ((tensorSheafUnit X L.val M.val).app U (l ⊗ₜ m) ⊗ₜ n) := by
  rw [← tensorLineBundleAssociator_hom_tmul X L M N U l m n]
  exact congrArg (fun k => k.val.app U
    ((tensorSheafUnit X (tensorSheaf X L.val M.val) N.val).app U
      ((tensorSheafUnit X L.val M.val).app U (l ⊗ₜ m) ⊗ₜ n)))
    (tensorLineBundleAssociator X L M N).hom_inv_id

/-- The native braiding interchanges the original pure factors. -/
theorem tensorSheafBraiding_hom_tmul (X : Scheme.{u}) (M N : X.Modules)
    (U : X.Opensᵒᵖ) (m : M.val.obj U) (n : N.val.obj U) :
    (tensorSheafBraiding X M N).hom.val.app U
      ((tensorSheafUnit X M N).app U (m ⊗ₜ n)) =
    (tensorSheafUnit X N M).app U (n ⊗ₜ m) := by
  exact sheafification_map_unit_apply X
    (CategoryTheory.BraidedCategory.braiding
      (C := PresheafOfModulesOfCommRing.{u} X.presheaf) M.val N.val).hom
    U (m ⊗ₜ[X.presheaf.obj U] n)

/-- Evaluation of an original pure tensor is the original functional applied to its argument. -/
theorem dualEvaluationIso_hom_tmul (X : Scheme.{u}) (L : LineBundle X)
    (U : X.Opensᵒᵖ) (d : (dualLineBundle X L).val.val.obj U) (l : L.val.val.obj U) :
    (dualEvaluationIso X L).hom.val.app U
      ((tensorSheafUnit X (dualLineBundle X L).val L.val).app U (d ⊗ₜ l)) =
    d.val.app (op (Over.mk (𝟙 U.unop))) l := by
  rw [dualEvaluationIso_hom]
  have h : tensorSheafUnit X (dualLineBundle X L).val L.val ≫
      (evaluationSheaf X L.val (SheafOfModules.unit X.ringCatSheaf)).val =
      evaluationPresheaf X L.val (SheafOfModules.unit X.ringCatSheaf) :=
    (_root_.PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)).apply_symm_apply _
  exact congrArg (fun k => k.app U (d ⊗ₜ[X.presheaf.obj U] l)) h
end AlgebraicGeometry.Scheme.Modules.Invertible
