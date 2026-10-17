/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.SimplexSingularTransferFunctor

/-! # Actual transfer identities, compositions, and signed all-degree singular maps -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite Motivic Motivic.PresheafWithTransfers

universe v u

namespace MotivicTest.SimplexSingularTransferFunctor

variable {k : Type u} [Field k] (P : PresheafWithTransfers.{v} k) {X Y Z : Cor k}

example : (Cor k)ᵒᵖ ⥤+ ChainComplex AddCommGrpCat.{v} ℕ := singularAdditiveFunctor P

example (α : X ⟶ Y) (β : Y ⟶ Z) :
    singularTransfer P (α ≫ β) = singularTransfer P β ≫ singularTransfer P α :=
  singularTransfer_comp P α β

example : singularTransfer P (𝟙 X) = 𝟙 (singularObj P X) := singularTransfer_id P X

example (α : X ⟶ Y) (n : ℕ) :
    ((singularAdditiveFunctor P).obj.map α.op).f n =
      transfer P (Cor.simplexExterior n α) := rfl

example (α β : X ⟶ Y) :
    (singularAdditiveFunctor P).obj.map (α - β).op =
      singularTransfer P α - singularTransfer P β := by
  change singularTransfer P (α - β) = singularTransfer P α - singularTransfer P β
  rw [sub_eq_add_neg, singularTransfer_add, singularTransfer_neg, sub_eq_add_neg]

end MotivicTest.SimplexSingularTransferFunctor
