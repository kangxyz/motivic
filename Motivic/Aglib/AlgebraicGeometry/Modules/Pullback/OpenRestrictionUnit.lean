/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction
public import Aglib.AlgebraicGeometry.Modules.Pullback.Unit
public import Aglib.AlgebraicGeometry.Modules.Restriction.Unit

/-! # Unit coherence for the native local pullback comparison -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Modules.Pullback.OpenRestriction

/-- The actual local pullback comparison preserves the canonical unit maps. -/
@[reassoc] theorem localPullbackIso_inv_unit {X Y : Scheme.{u}}
    (f : X ⟶ Y) (U : Y.Opens) :
    (localPullbackIso f U).inv.app (SheafOfModules.unit Y.ringCatSheaf) ≫
      (restrictFunctor (f ⁻¹ᵁ U).ι).map (pullbackUnitIso f).hom ≫
      (restrictUnitIso (f ⁻¹ᵁ U).ι).hom =
    (Scheme.Modules.pullback (f ∣_ U)).map (restrictUnitIso U.ι).hom ≫
      (pullbackUnitIso (f ∣_ U)).hom := by
  have he := restrictedAdjoint_eq f U
    (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)
  rw [← pullbackUnitIso_homEquiv f, Equiv.symm_apply_apply] at he
  rw [he]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  apply ((pullbackPushforwardAdjunction (f ∣_ U)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply,
    Adjunction.homEquiv_naturality_left, pullbackUnitIso_homEquiv]
  apply Scheme.Modules.hom_ext
  intro V
  ext r
  simp only [Scheme.Modules.Hom.comp_app, restrictedPushforwardMap_app,
    Scheme.Modules.pushforward_map_app, ConcreteCategory.comp_apply]
  simp only [pullbackUnitIso_homEquiv, restrictUnitIso_ι_hom_app_apply]
  erw [restrictUnitIso_ι_hom_app_apply]
  change X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op
      (f.app (U.ι ''ᵁ V) r) = (f ∣_ U).app V r
  rw [morphismRestrict_app]
  rfl

end AlgebraicGeometry.Scheme.Modules.Pullback.OpenRestriction
