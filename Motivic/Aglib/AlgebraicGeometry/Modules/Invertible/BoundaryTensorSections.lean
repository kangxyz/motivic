module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.DualTwistedIdealEvaluation
/-! # Literal tensor section balance on the full prescribed boundary -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
open scoped TensorProduct
universe u
namespace AlgebraicGeometry.Scheme.Modules.Invertible

private theorem tensor_balance {R : Type u} [CommRing R] {M N : Type u}
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (r : R) (m : M) (n : N) : (r • m) ⊗ₜ[R] n = m ⊗ₜ[R] (r • n) :=
  TensorProduct.smul_tmul r m n

private theorem tensor_right_smul {R : Type u} [CommRing R] {M N : Type u}
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (r : R) (m : M) (n : N) : m ⊗ₜ[R] (r • n) = r • (m ⊗ₜ[R] n) :=
  TensorProduct.tmul_smul r m n

def tensorUnitSection {X : Scheme.{u}} {M N : X.Modules}
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ M)
    (t : SheafOfModules.unit X.ringCatSheaf ⟶ N) :
    SheafOfModules.unit X.ringCatSheaf ⟶ tensorSheaf X M N :=
  (tensorSheafLeftUnit X (SheafOfModules.unit X.ringCatSheaf)).inv ≫ tensorSheafMap X s t

theorem tensorUnitSection_apply_one {X : Scheme.{u}} {M N : X.Modules}
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ M)
    (t : SheafOfModules.unit X.ringCatSheaf ⟶ N) (U : X.Opensᵒᵖ) :
    (tensorUnitSection s t).val.app U (1 : X.presheaf.obj U) =
      (tensorSheafUnit X M N).app U
        (s.val.app U (1 : X.presheaf.obj U) ⊗ₜ t.val.app U (1 : X.presheaf.obj U)) := by
  change (tensorSheafMap X s t).val.app U
    ((tensorSheafLeftUnit X _).inv.val.app U (1 : X.presheaf.obj U)) = _
  rw [tensorSheafLeftUnit_inv_apply, tensorSheafMap_tmul]

theorem tensorUnitSection_balance {X : Scheme.{u}} {M N : X.Modules}
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ M)
    (t : SheafOfModules.unit X.ringCatSheaf ⟶ N)
    (c : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    tensorUnitSection (c ≫ s) t = tensorUnitSection s (c ≫ t) := by
  apply (unitHomGlobalSectionsEquiv X _).injective
  change (tensorUnitSection (c ≫ s) t).val.app (op ⊤) (1 : Γ(X, ⊤)) =
    (tensorUnitSection s (c ≫ t)).val.app (op ⊤) (1 : Γ(X, ⊤))
  rw [tensorUnitSection_apply_one, tensorUnitSection_apply_one]
  have hs := (s.val.app (op ⊤)).hom.map_smul
    (show Γ(X, ⊤) from c.val.app (op ⊤) (1 : Γ(X, ⊤))) (1 : Γ(X, ⊤))
  have ht := (t.val.app (op ⊤)).hom.map_smul
    (show Γ(X, ⊤) from c.val.app (op ⊤) (1 : Γ(X, ⊤))) (1 : Γ(X, ⊤))
  simp only [smul_eq_mul, mul_one] at hs ht
  change (tensorSheafUnit X M N).app (op ⊤)
    (s.val.app (op ⊤) (c.val.app (op ⊤) (1 : Γ(X, ⊤))) ⊗ₜ _) =
    (tensorSheafUnit X M N).app (op ⊤)
    (_ ⊗ₜ t.val.app (op ⊤) (c.val.app (op ⊤) (1 : Γ(X, ⊤))))
  exact congrArg ((tensorSheafUnit X M N).app (op ⊤))
    ((congrArg (fun m => m ⊗ₜ t.val.app (op ⊤) (1 : Γ(X, ⊤))) hs).trans
      ((tensor_balance (R := X.presheaf.obj (op ⊤)) _ _ _).trans
        (congrArg (fun n => s.val.app (op ⊤) (1 : Γ(X, ⊤)) ⊗ₜ n) ht.symm)))

/-- Scalar action on the actual unit-domain tensor section. -/
theorem tensorUnitSection_precomp {X : Scheme.{u}} {M N : X.Modules}
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ M)
    (t : SheafOfModules.unit X.ringCatSheaf ⟶ N)
    (c : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    tensorUnitSection s (c ≫ t) = c ≫ tensorUnitSection s t := by
  apply (unitHomGlobalSectionsEquiv X _).injective
  change (tensorUnitSection s (c ≫ t)).val.app (op ⊤) (1 : Γ(X, ⊤)) =
    (tensorUnitSection s t).val.app (op ⊤) (c.val.app (op ⊤) (1 : Γ(X, ⊤)))
  rw [tensorUnitSection_apply_one]
  let r : Γ(X, ⊤) := c.val.app (op ⊤) (1 : Γ(X, ⊤))
  have ht := (t.val.app (op ⊤)).hom.map_smul r (1 : Γ(X, ⊤))
  have hf := ((tensorUnitSection s t).val.app (op ⊤)).hom.map_smul r (1 : Γ(X, ⊤))
  simp only [smul_eq_mul, mul_one] at ht hf
  change (tensorSheafUnit X M N).app (op ⊤)
      (s.val.app (op ⊤) (1 : Γ(X, ⊤)) ⊗ₜ t.val.app (op ⊤) r) = _
  rw [ht]
  rw [tensor_right_smul (R := X.presheaf.obj (op ⊤)),
    ((tensorSheafUnit X M N).app (op ⊤)).hom.map_smul]
  exact (congrArg (fun m => r • m) (tensorUnitSection_apply_one s t (op ⊤)).symm).trans hf.symm

/-- The prescribed divisor frame and coordinate ratio give the literal two-factor
boundary section equality used by the polynomial pencil. -/
theorem tensorUnitSection_prescribed_coordinate {X : Scheme.{u}} {T P S : X.Modules}
    (E : P ≅ SheafOfModules.unit X.ringCatSheaf)
    (δ : SheafOfModules.unit X.ringCatSheaf ⟶ P)
    (b : SheafOfModules.unit X.ringCatSheaf ⟶ T)
    (d : SheafOfModules.unit X.ringCatSheaf ⟶ S) :
    tensorUnitSection (tensorUnitSection b E.inv) ((δ ≫ E.hom) ≫ d) =
      tensorUnitSection (tensorUnitSection b δ) d := by
  apply (tensorUnitSection_balance (tensorUnitSection b E.inv) d (δ ≫ E.hom)).symm.trans
  have h := tensorUnitSection_precomp b E.inv (δ ≫ E.hom)
  have h' : (δ ≫ E.hom) ≫ E.inv = δ := by simp only [Category.assoc, Iso.hom_inv_id,
    Category.comp_id]
  rw [h'] at h
  exact congrArg (fun a => tensorUnitSection a d) h.symm

/-- The unit-domain tensor section in the native right-unit presentation. -/
theorem tensorUnitSection_eq_rightUnit {X : Scheme.{u}} {M N : X.Modules}
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ M)
    (t : SheafOfModules.unit X.ringCatSheaf ⟶ N) :
    tensorUnitSection s t = s ≫ (tensorSheafRightUnit X M).inv ≫
      tensorSheafMap X (𝟙 M) t := by
  apply (unitHomGlobalSectionsEquiv X _).injective
  change (tensorUnitSection s t).val.app (op ⊤) (1 : Γ(X, ⊤)) =
    (tensorSheafMap X (𝟙 M) t).val.app (op ⊤)
      ((tensorSheafRightUnit X M).inv.val.app (op ⊤)
        (s.val.app (op ⊤) (1 : Γ(X, ⊤))))
  rw [tensorUnitSection_apply_one, tensorSheafRightUnit_inv_apply, tensorSheafMap_tmul]
  rfl

/-- Normalize the producer's tensor-unit coefficient without changing the prescribed value. -/
theorem tensorUnitSection_normalized {X : Scheme.{u}} {T O P : X.Modules}
    (u : SheafOfModules.unit X.ringCatSheaf ⟶ tensorSheaf X T O)
    (e : O ≅ SheafOfModules.unit X.ringCatSheaf)
    (v : SheafOfModules.unit X.ringCatSheaf ⟶ P) :
    tensorUnitSection
      (u ≫ tensorSheafMap X (𝟙 T) e.hom ≫ (tensorSheafRightUnit X T).hom) v =
      u ≫ tensorSheafMap X (𝟙 T) (e.hom ≫ v) := by
  rw [tensorUnitSection_eq_rightUnit]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [tensorSheafMap_comp]
  simp only [Category.id_comp]
end AlgebraicGeometry.Scheme.Modules.Invertible
