/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.SimplexSingularTransferMaps

/-!
# Consumers of actual singular transfer chain maps

The consumers use arbitrary fields, arbitrary smooth correspondence objects,
all chain degrees, every original simplex operator, and signed multiplicities.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Motivic Motivic.PresheafWithTransfers
open scoped Simplicial

universe v u

namespace MotivicTest.SimplexSingularTransferMaps

variable {k : Type u} [Field k] (P : PresheafWithTransfers.{v} k)
  {X Y : Cor k} (α : X ⟶ Y)

example (n : ℕ) :
    (singularObj P X).X n = sections P (Cor.simplexProduct X n) := rfl

example {n m : SimplexCategory} (f : n ⟶ m) :
    (Cor.simplexProductCosimplicial X).map f ≫
        Cor.simplexExterior m.len α =
      Cor.simplexExterior n.len α ≫ (Cor.simplexProductCosimplicial Y).map f :=
  (Cor.simplexExteriorNatTrans α).naturality f

example (n : ℕ) :
    (singularTransfer P α).f n = transfer P (Cor.simplexExterior n α) := rfl

example (n : ℕ) :
    transfer P (Cor.simplexExterior (n + 1) α) ≫ (singularObj P X).d (n + 1) n =
      (singularObj P Y).d (n + 1) n ≫ transfer P (Cor.simplexExterior n α) :=
  singularTransfer_comm P α (n + 1) n

example (n : ℕ) :
    (singularObj P X).d (n + 2) (n + 1) ≫ (singularObj P X).d (n + 1) n = 0 :=
  (singularObj P X).d_comp_d _ _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
example (n : ℕ) :
    (singularObj P X).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        transfer P ((Cor.graphFunctor k).map (SmoothSite.productMap (𝟙 X.toSmoothSite)
          ((AlgebraicSimplex.cosimplicialSmoothSite k).δ i))) :=
  singularObj_d P X n

example : singularTransfer P ((-3 : ℤ) • α) = (-3 : ℤ) • singularTransfer P α := by
  simp

example (β : X ⟶ Y) :
    singularTransfer P (α + β) = singularTransfer P α + singularTransfer P β := by
  simp

example : singularTransfer P (0 : X ⟶ Y) = 0 := by simp

end MotivicTest.SimplexSingularTransferMaps
