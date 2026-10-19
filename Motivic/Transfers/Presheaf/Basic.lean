/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Basic
public import Mathlib.CategoryTheory.Preadditive.Opposite
public import Mathlib.Algebra.Category.Grp.Preadditive

/-!
# Abelian presheaves with transfers

A presheaf with transfers over an arbitrary field is an additive contravariant
functor from the actual finite-correspondence category to abelian groups.
We use Mathlib's bundled additive functors, so morphisms are all natural
transformations and the category is preadditive. The transfer action is the
actual functor map on signed correspondence cycles, including negative integer
multiplicities. No connectedness assumption is made on the smooth objects.

Restriction along any functor into `Cor k` gives an ordinary presheaf. This is
the interface for restriction along the graph functor once that functor is
available; it does not assume an unproved graph-composition law or assert any
sheafification result.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe v u v' u'

namespace Motivic

/-- Abelian presheaves with transfers on the actual correspondence category. -/
abbrev PresheafWithTransfers (k : Type u) [Field k] :=
  (Cor k)ᵒᵖ ⥤+ AddCommGrpCat.{v}

namespace PresheafWithTransfers

variable {k : Type u} [Field k]

/-- Forget additivity as a bundled property, retaining the entire presheaf. -/
abbrev forget : PresheafWithTransfers.{v} k ⥤ (Cor k)ᵒᵖ ⥤ AddCommGrpCat.{v} :=
  AdditiveFunctor.forget _ _

/-- The abelian group of sections on a smooth correspondence object. -/
abbrev sections (P : PresheafWithTransfers.{v} k) (X : Cor k) : AddCommGrpCat.{v} :=
  P.obj.obj (op X)

/-- The contravariant transfer associated to an actual signed correspondence. -/
abbrev transfer (P : PresheafWithTransfers.{v} k) {X Y : Cor k} (α : X ⟶ Y) :
    sections P Y ⟶ sections P X :=
  P.obj.map α.op

@[simp]
theorem transfer_id (P : PresheafWithTransfers.{v} k) (X : Cor k) :
    transfer P (𝟙 X) = 𝟙 (sections P X) :=
  P.obj.map_id (op X)

/-- Composition of actual incidence Tor cycles acts contravariantly. -/
@[simp]
theorem transfer_comp (P : PresheafWithTransfers.{v} k) {X Y Z : Cor k}
    (α : X ⟶ Y) (β : Y ⟶ Z) :
    transfer P (α ≫ β) = transfer P β ≫ transfer P α :=
  P.obj.map_comp β.op α.op

@[simp]
theorem transfer_zero (P : PresheafWithTransfers.{v} k) (X Y : Cor k) :
    transfer P (0 : X ⟶ Y) = 0 :=
  P.obj.map_zero _ _

@[simp]
theorem transfer_add (P : PresheafWithTransfers.{v} k) {X Y : Cor k}
    (α β : X ⟶ Y) : transfer P (α + β) = transfer P α + transfer P β :=
  P.obj.map_add

@[simp]
theorem transfer_neg (P : PresheafWithTransfers.{v} k) {X Y : Cor k} (α : X ⟶ Y) :
    transfer P (-α) = -transfer P α :=
  P.obj.map_neg

@[simp]
theorem transfer_sub (P : PresheafWithTransfers.{v} k) {X Y : Cor k}
    (α β : X ⟶ Y) : transfer P (α - β) = transfer P α - transfer P β :=
  P.obj.map_sub

@[simp]
theorem transfer_zsmul (P : PresheafWithTransfers.{v} k) {X Y : Cor k}
    (n : ℤ) (α : X ⟶ Y) : transfer P (n • α) = n • transfer P α :=
  P.obj.map_zsmul

/-- A morphism of presheaves with transfers commutes with each transfer. -/
@[reassoc]
theorem transfer_naturality {P Q : PresheafWithTransfers.{v} k} (η : P ⟶ Q)
    {X Y : Cor k} (α : X ⟶ Y) :
    transfer P α ≫ η.hom.app (op X) = η.hom.app (op Y) ≫ transfer Q α :=
  η.hom.naturality α.op

variable {C : Type u'} [Category.{v'} C]

/-- Restriction to ordinary presheaves along a given functor into correspondences. -/
def restrictAlong (G : C ⥤ Cor k) :
    PresheafWithTransfers.{v} k ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{v} :=
  forget ⋙ (Functor.whiskeringLeft _ _ _).obj G.op

instance (G : C ⥤ Cor k) : (restrictAlong.{v} G).Additive := by
  dsimp [restrictAlong]
  infer_instance

@[simp]
theorem restrictAlong_obj_obj (G : C ⥤ Cor k) (P : PresheafWithTransfers.{v} k)
    (X : Cᵒᵖ) : ((restrictAlong G).obj P).obj X = sections P (G.obj X.unop) := rfl

@[simp]
theorem restrictAlong_obj_map (G : C ⥤ Cor k) (P : PresheafWithTransfers.{v} k)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ((restrictAlong G).obj P).map f = transfer P (G.map f.unop) := rfl

@[simp]
theorem restrictAlong_map_app (G : C ⥤ Cor k) {P Q : PresheafWithTransfers.{v} k}
    (η : P ⟶ Q) (X : Cᵒᵖ) :
    ((restrictAlong G).map η).app X = η.hom.app (op (G.obj X.unop)) := rfl

end PresheafWithTransfers

end Motivic
