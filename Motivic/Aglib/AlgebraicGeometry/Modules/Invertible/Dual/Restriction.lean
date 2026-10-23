/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Dual.PerfectPairing
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Restriction
public import Aglib.AlgebraicGeometry.Modules.Restriction.Unit
/-! # Open restriction of actual line duals preserves evaluation -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct
universe u
namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- The literal restriction of an actual line bundle. -/
def restrictLineBundle {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (L : LineBundle X) : LineBundle U :=
  ⟨(restrictFunctor j).obj L.val, isLocallyRankOne_of_iso _
    ((restrictFunctorIsoPullback j).symm.app L.val)
    (pullback_locallyRankOne j L.val L.property)⟩

/-- The original evaluation restricted through native tensor and unit comparisons. -/
def restrictedDualEvaluationIso {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (L : LineBundle X) :
    tensorSheaf U ((restrictFunctor j).obj (dualLineBundle X L).val)
      ((restrictFunctor j).obj L.val) ≅ SheafOfModules.unit U.ringCatSheaf :=
  tensorRestrictionIso j (dualLineBundle X L).val L.val ≪≫
    (restrictFunctor j).mapIso (dualEvaluationIso X L) ≪≫ restrictUnitIso j

/-- The canonical actual dual comparison, constructed from the original evaluation. -/
def restrictDualIso {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (L : LineBundle X) :
    (restrictFunctor j).obj (dualLineBundle X L).val ≅
      (dualLineBundle U (restrictLineBundle j L)).val :=
  perfectPairingDualIso U (restrictLineBundle j (dualLineBundle X L))
    (restrictLineBundle j L) (restrictedDualEvaluationIso j L)

/-- Restricting the dual retains the literal evaluation, not only its Picard class. -/
@[reassoc] theorem restrictDualIso_evaluation {X U : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (L : LineBundle X) :
    tensorSheafMap U (restrictDualIso j L).hom (𝟙 ((restrictFunctor j).obj L.val)) ≫
      (dualEvaluationIso U (restrictLineBundle j L)).hom =
    (tensorRestrictionIso j (dualLineBundle X L).val L.val).hom ≫
      (restrictFunctor j).map (dualEvaluationIso X L).hom ≫ (restrictUnitIso j).hom :=
  perfectPairingDualIso_pairing U (restrictLineBundle j (dualLineBundle X L))
    (restrictLineBundle j L) (restrictedDualEvaluationIso j L)

/-- Evaluation uniquely determines an actual section of the dual line. -/
theorem dualSection_eq_of_evaluation (X : Scheme.{u}) (L : LineBundle X)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ (dualLineBundle X L).val)
    (h : tensorSheafMap X a (𝟙 L.val) ≫ (dualEvaluationIso X L).hom =
      tensorSheafMap X b (𝟙 L.val) ≫ (dualEvaluationIso X L).hom) : a = b := by
  let e := (InternalHom.globalHomEquiv X L.val (SheafOfModules.unit X.ringCatSheaf)).trans
    (unitHomGlobalSectionsEquiv X (dualSheaf X L.val)).symm
  obtain ⟨φ, rfl⟩ := e.surjective a
  obtain ⟨ψ, rfl⟩ := e.surjective b
  change tensorSheafMap X (canonicalDualHom X L.val φ) (𝟙 L.val) ≫ _ =
    tensorSheafMap X (canonicalDualHom X L.val ψ) (𝟙 L.val) ≫ _ at h
  rw [dualEvaluationIso_hom, canonicalDualHom_evaluation,
    canonicalDualHom_evaluation] at h
  have hh := (cancel_epi (tensorSheafLeftUnit X L.val).hom).mp h
  exact congrArg e hh

/-- The original divisor's canonical section remains the same actual canonical dual section. -/
theorem restrictDualIso_canonicalDualHom {X : Scheme.{u}} (U : X.Opens)
    (L : LineBundle X) (φ : L.val ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (restrictUnitIso U.ι).inv ≫ (restrictFunctor U.ι).map (canonicalDualHom X L.val φ) ≫
      (restrictDualIso U.ι L).hom =
    canonicalDualHom U.toScheme (restrictLineBundle U.ι L).val
      ((restrictFunctor U.ι).map φ ≫ (restrictUnitIso U.ι).hom) := by
  apply dualSection_eq_of_evaluation U.toScheme (restrictLineBundle U.ι L)
  have hc := tensorSheafMap_comp U.toScheme
    ((restrictUnitIso U.ι).inv ≫ (restrictFunctor U.ι).map (canonicalDualHom X L.val φ))
    (𝟙 ((restrictFunctor U.ι).obj L.val)) (restrictDualIso U.ι L).hom
    (𝟙 ((restrictFunctor U.ι).obj L.val))
  simp only [Category.id_comp, Category.assoc] at hc
  erw [← hc, Category.assoc]
  rw [restrictDualIso_evaluation]
  have he := canonicalDualHom_evaluation U.toScheme (restrictLineBundle U.ι L).val
    ((restrictFunctor U.ι).map φ ≫ (restrictUnitIso U.ι).hom)
  rw [← dualEvaluationIso_hom U.toScheme (restrictLineBundle U.ι L)] at he
  erw [he]
  apply moduleTensor_hom_ext
  intro V r m
  change ((restrictUnitIso U.ι).hom).val.app (op V)
    (((restrictFunctor U.ι).map (dualEvaluationIso X L).hom).val.app (op V)
      ((restrictTensorMap X U (dualLineBundle X L).val L.val).val.app (op V)
        ((tensorSheafMap U.toScheme
          ((restrictUnitIso U.ι).inv ≫
            (restrictFunctor U.ι).map (canonicalDualHom X L.val φ))
          (𝟙 ((restrictFunctor U.ι).obj L.val))).val.app (op V)
          ((tensorSheafUnit U.toScheme _ _).app (op V) (r ⊗ₜ m))))) = _
  rw [tensorSheafMap_tmul]
  erw [restrictTensorMap_tmul X U (dualLineBundle X L).val L.val]
  have hr : (restrictUnitIso U.ι).inv.val.app (op V) r = r := by
    change (U.ι.appIso V).inv r = r
    rw [Scheme.Opens.ι_appIso]
    rfl
  change (restrictUnitIso U.ι).hom.app V
    ((dualEvaluationIso X L).hom.val.app (op (U.ι ''ᵁ V))
      ((tensorSheafUnit X _ _).app (op (U.ι ''ᵁ V))
        ((canonicalDualHom X L.val φ).val.app (op (U.ι ''ᵁ V))
          ((restrictUnitIso U.ι).inv.val.app (op V) r) ⊗ₜ m))) = _
  rw [hr, restrictUnitIso_ι_hom_app_apply]
  have h := congrArg (fun f => f.val.app (op (U.ι ''ᵁ V))
    ((tensorSheafUnit X _ _).app (op (U.ι ''ᵁ V)) (r ⊗ₜ m)))
      (canonicalDualHom_evaluation X L.val φ)
  simp only [SheafOfModules.comp_val, _root_.PresheafOfModules.comp_app,
    ModuleCat.comp_apply] at h
  rw [tensorSheafMap_tmul] at h
  rw [dualEvaluationIso_hom]
  erw [h]
  change φ.val.app (op (U.ι ''ᵁ V))
    ((tensorSheafLeftUnit X L.val).hom.val.app (op (U.ι ''ᵁ V)) _) =
    (restrictUnitIso U.ι).hom.app V
      (φ.val.app (op (U.ι ''ᵁ V))
        ((tensorSheafLeftUnit U.toScheme ((restrictFunctor U.ι).obj L.val)).hom.val.app
          (op V) _))
  dsimp only [moduleTensorSection]
  erw [tensorSheafLeftUnit_tmul, tensorSheafLeftUnit_tmul]
  rw [restrictUnitIso_ι_hom_app_apply]
  change X.presheaf.obj (op (U.ι ''ᵁ V)) at r
  change L.val.val.obj (op (U.ι ''ᵁ V)) at m
  change φ.val.app (op (U.ι ''ᵁ V)) (r • m) =
    φ.val.app (op (U.ι ''ᵁ V)) ((U.ι.appIso V).inv r • m)
  rw [Scheme.Opens.ι_appIso]
  rfl

end AlgebraicGeometry.Scheme.Modules.Invertible
