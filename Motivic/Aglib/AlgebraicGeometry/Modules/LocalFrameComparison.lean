/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction
public import Aglib.AlgebraicGeometry.Modules.Pullback.Unit

/-! # Equality of actual restricted module morphisms in supplied local frames -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Pullback.OpenRestriction

namespace AlgebraicGeometry.Scheme.Modules
universe u

private theorem comp_apply {X : Scheme.{u}} {M N P : X.Modules}
    (a : M ⟶ N) (b : N ⟶ P) (V : X.Opensᵒᵖ) (s : M.val.obj V) :
    (a ≫ b).val.app V s = b.val.app V (a.val.app V s) := rfl

private theorem pushforward_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : X.Modules} (a : M ⟶ N) (V : Y.Opensᵒᵖ)
    (s : ((pushforward f).obj M).val.obj V) :
    ((pushforward f).map a).val.app V s = a.val.app (op (f ⁻¹ᵁ V.unop)) s := rfl

private theorem restrict_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] {M N : Y.Modules} (a : M ⟶ N) (V : X.Opensᵒᵖ)
    (s : ((restrictFunctor f).obj M).val.obj V) :
    ((restrictFunctor f).map a).val.app V s = a.val.app (op (f ''ᵁ V.unop)) s := rfl

private theorem unit_pushforward_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.Opensᵒᵖ) (s : Γ(Y, V.unop)) :
    (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom).val.app V s =
      (f.app V.unop).hom s := rfl

/-- An equality of section maps gives the corresponding actual local-frame equality. -/
theorem localFrameComparison_of_apply {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    {M : Y.Modules} {N : X.Modules}
    (eM : (restrictFunctor U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (eN : (restrictFunctor (f ⁻¹ᵁ U).ι).obj N ≅
      SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf)
    (φ : M ⟶ (pushforward f).obj N)
    (h : ∀ (V : U.toScheme.Opens) (s : Γ((restrictFunctor U.ι).obj M, V)),
      eN.hom.val.app (op ((f ∣_ U) ⁻¹ᵁ V))
        (N.val.map (eqToHom (image_morphismRestrict_preimage f U V)).op
          (φ.val.app (op (U.ι ''ᵁ V)) s)) =
      ((f ∣_ U).app V).hom (eM.hom.val.app (op V) s)) :
    (restrictFunctor U.ι).map φ ≫ restrictedPushforwardMap f U N ≫
        (pushforward (f ∣_ U)).map eN.hom =
      eM.hom ≫ SheafOfModules.unitToPushforwardObjUnit (f ∣_ U).toRingCatSheafHom := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext s
  simp only [comp_apply]
  rw [pushforward_apply, restrictedPushforwardMap_apply, restrict_apply]
  exact (h V.unop s).trans (unit_pushforward_apply (f ∣_ U) V _).symm

end AlgebraicGeometry.Scheme.Modules
