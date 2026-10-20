/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.Representable

/-!
# Additive Yoneda for presheaves with transfers

A section of an abelian presheaf with transfers on `X` determines a morphism
from the actual representable of `X`: a correspondence acts on that section by
its transfer. Evaluation at the full componentwise identity cycle is inverse,
yielding an additive equivalence. Naturality is stated for both a presheaf
morphism and a correspondence of representing objects.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace Motivic.PresheafWithTransfers

variable {k : Type u} [Field k]

/-- A section determines a morphism from the actual representable by transfer. -/
def sectionHom (P : PresheafWithTransfers.{u} k) (X : Cor k) (s : sections P X) :
    (representable k).obj X ⟶ P :=
  ObjectProperty.homMk
    { app Y := by
        change AddCommGrpCat.of (Y.unop ⟶ X) ⟶ sections P Y.unop
        exact AddCommGrpCat.ofHom
          { toFun α := transfer P α s
            map_zero' := by
              rw [transfer_zero]
              rfl
            map_add' α β := by
              rw [transfer_add]
              rfl }
      naturality Y Z f := by
        apply AddCommGrpCat.ext
        intro α
        change Y.unop ⟶ X at α
        change transfer P (f.unop ≫ α) s = transfer P f.unop (transfer P α s)
        rw [transfer_comp]
        rfl }

@[simp↓]
theorem sectionHom_app (P : PresheafWithTransfers.{u} k) (X Y : Cor k)
    (s : sections P X) (α : Y ⟶ X) :
    (sectionHom P X s).hom.app (op Y) α = transfer P α s := rfl

/-- Additive Yoneda, evaluated at the actual componentwise diagonal identity. -/
def yonedaAddEquiv (P : PresheafWithTransfers.{u} k) (X : Cor k) :
    ((representable k).obj X ⟶ P) ≃+ sections P X where
  toFun η := η.hom.app (op X) (𝟙 X)
  invFun := sectionHom P X
  left_inv η := by
    apply ObjectProperty.hom_ext
    ext Y α
    change Y.unop ⟶ X at α
    change transfer P α (η.hom.app (op X) (𝟙 X)) = η.hom.app Y α
    have h := congrArg (fun f => f (𝟙 X)) (η.hom.naturality α.op)
    change η.hom.app Y (α ≫ 𝟙 X) = transfer P α (η.hom.app (op X) (𝟙 X)) at h
    simpa only [Category.comp_id] using h.symm
  right_inv s := by
    change transfer P (𝟙 X) s = s
    rw [transfer_id]
    rfl
  map_add' _ _ := rfl

@[simp]
theorem yonedaAddEquiv_apply (P : PresheafWithTransfers.{u} k) (X : Cor k)
    (η : (representable k).obj X ⟶ P) :
    yonedaAddEquiv P X η = η.hom.app (op X) (𝟙 X) := rfl

@[simp]
theorem yonedaAddEquiv_symm_apply (P : PresheafWithTransfers.{u} k) (X : Cor k)
    (s : sections P X) : (yonedaAddEquiv P X).symm s = sectionHom P X s := rfl

/-- Yoneda evaluation commutes with a morphism of presheaves with transfers. -/
theorem yonedaAddEquiv_naturality {P Q : PresheafWithTransfers.{u} k} (η : P ⟶ Q)
    (X : Cor k) (f : (representable k).obj X ⟶ P) :
    yonedaAddEquiv Q X (f ≫ η) = η.hom.app (op X) (yonedaAddEquiv P X f) := rfl

/-- Yoneda evaluation is contravariant in an actual correspondence. -/
theorem yonedaAddEquiv_naturality_left (P : PresheafWithTransfers.{u} k)
    {X Y : Cor k} (α : X ⟶ Y) (f : (representable k).obj Y ⟶ P) :
    yonedaAddEquiv P X ((representable k).map α ≫ f) =
      transfer P α (yonedaAddEquiv P Y f) := by
  change f.hom.app (op X) ((𝟙 X) ≫ α) =
    transfer P α (f.hom.app (op Y) (𝟙 Y))
  rw [Category.id_comp]
  have h := congrArg (fun g => g (𝟙 Y)) (f.hom.naturality α.op)
  change f.hom.app (op X) (α ≫ 𝟙 Y) =
    transfer P α (f.hom.app (op Y) (𝟙 Y)) at h
  simpa only [Category.comp_id] using h

end Motivic.PresheafWithTransfers
