/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Unit
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorFunctorAssociator.Sections

/-! # Right-unit compatibility for the actual tensor pullback -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.Modules

def tensorSheafRightUnit (X : Scheme.{u}) (M : X.Modules) :
    tensorSheaf X M (SheafOfModules.unit X.ringCatSheaf) ≅ M :=
  (SheafOfModulesOfCommRing.tensorRightUnitIso X.sheaf).app M

theorem tensorSheafRightUnit_tmul (X : Scheme.{u}) (M : X.Modules) (U : X.Opensᵒᵖ)
    (m : M.val.obj U) (r : X.presheaf.obj U) :
    (tensorSheafRightUnit X M).hom.val.app U
      ((tensorSheafUnit X M (SheafOfModules.unit X.ringCatSheaf)).app U (m ⊗ₜ r)) = r • m :=
  tensorRightUnitIso_hom_section X M U.unop m r

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
theorem pushforwardTensorMap_rightUnit (M : Y.Modules) :
    tensorSheafMap Y ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
        (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
      pushforwardTensorMap f ((Scheme.Modules.pullback f).obj M)
        (SheafOfModules.unit X.ringCatSheaf) ≫
      (Scheme.Modules.pushforward f).map
        (tensorSheafRightUnit X ((Scheme.Modules.pullback f).obj M)).hom =
    (tensorSheafRightUnit Y M).hom ≫
      (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M := by
  apply (_root_.PresheafOfModules.sheafificationHomEquiv (𝟙 Y.ringCatSheaf.obj)).injective
  ext U : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m r
  change Y.presheaf.obj U at r
  change M.val.obj U at m
  change (tensorSheafRightUnit X ((Scheme.Modules.pullback f).obj M)).hom.val.app
    (op (f ⁻¹ᵁ U.unop))
    ((pushforwardTensorMap f ((Scheme.Modules.pullback f).obj M)
      (SheafOfModules.unit X.ringCatSheaf)).val.app U
      ((tensorSheafMap Y ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
        (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)).val.app U
          ((tensorSheafUnit Y M (SheafOfModules.unit Y.ringCatSheaf)).app U (m ⊗ₜ r)))) =
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app U
      ((tensorSheafRightUnit Y M).hom.val.app U
        ((tensorSheafUnit Y M (SheafOfModules.unit Y.ringCatSheaf)).app U (m ⊗ₜ r)))
  have h₁ := tensorSheafMap_tmul Y
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
    (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) U m r
  have h₂ := pushforwardTensorMap_tmul f ((Scheme.Modules.pullback f).obj M)
    (SheafOfModules.unit X.ringCatSheaf) U
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app U m) (f.app U.unop r)
  have h₃ := tensorSheafRightUnit_tmul X ((Scheme.Modules.pullback f).obj M)
    (op (f ⁻¹ᵁ U.unop))
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app U m) (f.app U.unop r)
  have h₄ := tensorSheafRightUnit_tmul Y M U m r
  exact (congrArg (fun z ↦
      (tensorSheafRightUnit X ((Scheme.Modules.pullback f).obj M)).hom.val.app
        (op (f ⁻¹ᵁ U.unop)) z)
    ((congrArg (fun z ↦ (pushforwardTensorMap f ((Scheme.Modules.pullback f).obj M)
      (SheafOfModules.unit X.ringCatSheaf)).val.app U z) h₁).trans h₂)).trans
    (h₃.trans
      (((((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app U).hom.map_smul
        r m).symm.trans
      (congrArg
        (fun z ↦ ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app U z)
        h₄.symm)))

theorem pullbackTensorMap_rightUnit (M : Y.Modules) :
    pullbackTensorMap f M (SheafOfModules.unit Y.ringCatSheaf) ≫
        tensorSheafMap X (𝟙 ((Scheme.Modules.pullback f).obj M)) (pullbackUnitIso f).hom ≫
        (tensorSheafRightUnit X ((Scheme.Modules.pullback f).obj M)).hom =
      (Scheme.Modules.pullback f).map (tensorSheafRightUnit Y M).hom := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, pullbackTensorMap_adjoint, Functor.map_comp]
  simp only [Category.assoc]
  have hn := pushforwardTensorMap_naturality_assoc f (𝟙 ((Scheme.Modules.pullback f).obj M))
    (pullbackUnitIso f).hom
    ((Scheme.Modules.pushforward f).map
      (tensorSheafRightUnit X ((Scheme.Modules.pullback f).obj M)).hom)
  rw [← hn]
  rw [tensorSheafMap_comp_assoc]
  have hu := pullbackUnitIso_homEquiv f
  change (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
      (SheafOfModules.unit Y.ringCatSheaf) ≫
    (Scheme.Modules.pushforward f).map (pullbackUnitIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom at hu
  rw [hu]
  exact (pushforwardTensorMap_rightUnit f M).trans
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality _)


end AlgebraicGeometry.Scheme.Modules
