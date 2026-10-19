/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.InternalHom.Gluing
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Hom
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Unit
public import Aglib.AlgebraicGeometry.Modules.Invertible.PullbackTensor.Local

/-! # Literal evaluation of the original canonical divisor section -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.Modules.Invertible
variable (X : Scheme.{u}) (M : X.Modules)

/-- The unit-to-dual morphism of an actual functional, with no change of section. -/
def canonicalDualHom (φ : M ⟶ SheafOfModules.unit X.ringCatSheaf) :
    SheafOfModules.unit X.ringCatSheaf ⟶ dualSheaf X M :=
  (unitHomGlobalSectionsEquiv X (dualSheaf X M)).symm
    (InternalHom.globalHomEquiv X M (SheafOfModules.unit X.ringCatSheaf) φ)

/-- On a pure tensor, canonical evaluation is the original functional. -/
theorem canonicalDualHom_evaluation
    (φ : M ⟶ SheafOfModules.unit X.ringCatSheaf) :
    tensorSheafMap X (canonicalDualHom X M φ) (𝟙 M) ≫
        evaluationSheaf X M (SheafOfModules.unit X.ringCatSheaf) =
      (tensorSheafLeftUnit X M).hom ≫ φ := by
  apply (_root_.PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)).injective
  ext U : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro r m
  change X.presheaf.obj U at r
  change M.val.obj U at m
  change (evaluationSheaf X M (SheafOfModules.unit X.ringCatSheaf)).val.app U
      ((tensorSheafMap X (canonicalDualHom X M φ) (𝟙 M)).val.app U
        ((tensorSheafUnit X (SheafOfModules.unit X.ringCatSheaf) M).app U (r ⊗ₜ m))) =
    φ.val.app U ((tensorSheafLeftUnit X M).hom.val.app U
      ((tensorSheafUnit X (SheafOfModules.unit X.ringCatSheaf) M).app U (r ⊗ₜ m)))
  rw [tensorSheafMap_tmul, tensorSheafLeftUnit_tmul]
  change (evaluationSheaf X M (SheafOfModules.unit X.ringCatSheaf)).val.app U
      ((tensorSheafUnit X (dualSheaf X M) M).app U
        ((canonicalDualHom X M φ).val.app U r ⊗ₜ m)) = _
  have he : tensorSheafUnit X (dualSheaf X M) M ≫
      (evaluationSheaf X M (SheafOfModules.unit X.ringCatSheaf)).val =
        evaluationPresheaf X M (SheafOfModules.unit X.ringCatSheaf) :=
    (_root_.PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)).apply_symm_apply _
  have he' := congrArg (fun k => k.app U
    ((canonicalDualHom X M φ).val.app U r ⊗ₜ m)) he
  change (evaluationSheaf X M (SheafOfModules.unit X.ringCatSheaf)).val.app U
      ((tensorSheafUnit X (dualSheaf X M) M).app U
        ((canonicalDualHom X M φ).val.app U r ⊗ₜ m)) = _ at he'
  rw [he']
  change ((canonicalDualHom X M φ).val.app U r).val.app (op (Over.mk (𝟙 U.unop))) m = _
  have hc := unitHomGlobalSectionsEquiv_symm_app X (dualSheaf X M)
    (InternalHom.globalHomEquiv X M (SheafOfModules.unit X.ringCatSheaf) φ) U.unop r
  change (canonicalDualHom X M φ).val.app U r = _ at hc
  rw [hc]
  change X.presheaf.map (𝟙 U.unop).op r *
    (show X.presheaf.obj U from φ.val.app U m) = φ.val.app U (r • m)
  simp

/-- Pullback evaluation of the same canonical section is the literal pulled functional. -/
theorem pullback_canonicalDualHom_evaluation {W : Scheme.{u}} (f : W ⟶ X)
    (L : LineBundle X) (φ : L.val ⟶ SheafOfModules.unit X.ringCatSheaf) :
    tensorSheafMap W ((Scheme.Modules.pullback f).map (canonicalDualHom X L.val φ))
        (𝟙 ((Scheme.Modules.pullback f).obj L.val)) ≫
      (PullbackTensor.Local.pullbackLineBundleTensorIso f (dualLineBundle X L) L).inv ≫
      (Scheme.Modules.pullback f).map (dualEvaluationIso X L).hom ≫ (pullbackUnitIso f).hom =
    tensorSheafMap W (pullbackUnitIso f).hom (𝟙 ((Scheme.Modules.pullback f).obj L.val)) ≫
      (tensorSheafLeftUnit W ((Scheme.Modules.pullback f).obj L.val)).hom ≫
      (Scheme.Modules.pullback f).map φ ≫ (pullbackUnitIso f).hom := by
  have := pullbackTensorMap_leftUnit_isIso f L.val
  apply (cancel_epi (pullbackTensorMap f (SheafOfModules.unit X.ringCatSheaf) L.val)).mp
  have hn := pullbackTensorMap_naturality f (canonicalDualHom X L.val φ) (𝟙 L.val)
  erw [CategoryTheory.Functor.map_id] at hn
  rw [← Category.assoc, ← hn]
  simp only [Category.assoc]
  change (Scheme.Modules.pullback f).map (tensorSheafMap X (canonicalDualHom X L.val φ) (𝟙 L.val)) ≫
      (PullbackTensor.Local.pullbackLineBundleTensorIso f (dualLineBundle X L) L).hom ≫ _ = _
  rw [Iso.hom_inv_id_assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc, dualEvaluationIso_hom, canonicalDualHom_evaluation]
  rw [CategoryTheory.Functor.map_comp]
  rw [← pullbackTensorMap_leftUnit f L.val]
  simp only [Category.assoc]

end AlgebraicGeometry.Scheme.Modules.Invertible
