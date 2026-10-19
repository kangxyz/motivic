/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Exterior.Simplex.Functor
public import Motivic.AlgebraicGeometry.Correspondences.Singular.Maps

/-!
# The all-degree singular functor with actual transfers

The already constructed transfer chain maps preserve identities and reverse
composition because their actual exterior cycles do. This bundles the full
all-degree singular complex as an additive contravariant functor on `Cor k`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open scoped Simplicial

universe v u

namespace Motivic

namespace Cor

variable {k : Type u} [Field k]

/-- Actual exterior correspondences make the product simplex functorial in `Cor`. -/
def simplexProductCosimplicialFunctor : Cor k ⥤ CosimplicialObject (Cor k) where
  obj X := simplexProductCosimplicial X
  map α := simplexExteriorNatTrans α
  map_id X := by
    ext n : 1
    exact simplexExterior_id n.len X
  map_comp α β := by
    ext n : 1
    exact simplexExterior_comp n.len α β

end Cor

namespace PresheafWithTransfers

variable {k : Type u} [Field k]

/-- The actual componentwise identity acts identically in every singular degree. -/
@[simp] theorem singularTransfer_id (P : PresheafWithTransfers.{v} k) (X : Cor k) :
    singularTransfer P (𝟙 X) = 𝟙 (singularObj P X) := by
  ext n : 1
  change transfer P (Cor.simplexExterior n (𝟙 X)) = 𝟙 _
  rw [Cor.simplexExterior_id, transfer_id]

/-- Actual signed correspondence composition acts contravariantly on the whole chain complex. -/
@[simp] theorem singularTransfer_comp (P : PresheafWithTransfers.{v} k) {X Y Z : Cor k}
    (α : X ⟶ Y) (β : Y ⟶ Z) :
    singularTransfer P (α ≫ β) = singularTransfer P β ≫ singularTransfer P α := by
  ext n : 1
  change transfer P (Cor.simplexExterior n (α ≫ β)) =
    transfer P (Cor.simplexExterior n β) ≫ transfer P (Cor.simplexExterior n α)
  rw [Cor.simplexExterior_comp, transfer_comp]

/-- The existing all-degree singular complex with its genuine contravariant transfer maps. -/
def singularFunctor (P : PresheafWithTransfers.{v} k) :
    (Cor k)ᵒᵖ ⥤ ChainComplex AddCommGrpCat.{v} ℕ where
  obj X := singularObj P X.unop
  map α := singularTransfer P α.unop
  map_id X := singularTransfer_id P X.unop
  map_comp α β := singularTransfer_comp P β.unop α.unop

@[simp] theorem singularFunctor_obj (P : PresheafWithTransfers.{v} k) (X : Cor k) :
    (singularFunctor P).obj (op X) = singularObj P X := rfl

@[simp] theorem singularFunctor_map (P : PresheafWithTransfers.{v} k) {X Y : Cor k}
    (α : X ⟶ Y) : (singularFunctor P).map α.op = singularTransfer P α := rfl

instance singularFunctor_additive (P : PresheafWithTransfers.{v} k) :
    (singularFunctor P).Additive where
  map_add := by
    intro X Y α β
    change singularTransfer P ((α + β).unop) =
      singularTransfer P α.unop + singularTransfer P β.unop
    exact singularTransfer_add P α.unop β.unop

/-- The all-degree singular construction is additive on the actual correspondence category. -/
def singularAdditiveFunctor (P : PresheafWithTransfers.{v} k) :
    (Cor k)ᵒᵖ ⥤+ ChainComplex AddCommGrpCat.{v} ℕ :=
  AdditiveFunctor.of (singularFunctor P)

end PresheafWithTransfers

end Motivic
