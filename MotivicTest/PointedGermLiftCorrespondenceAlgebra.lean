/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.PointedGermLiftCorrespondenceAlgebra
public import Lean.Util.CollectAxioms

/-! Actual witness algebra in signed correspondences, with a fixed original germ tuple. -/
@[expose] public noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Motivic Motivic.PresheafWithTransfers
universe u
namespace MotivicTest.PointedGermLiftCorrespondenceAlgebra
variable (k : Type u) [Field k] (P : PresheafWithTransfers.{u + 1} k)
  {X Y : SmoothSite (Spec (.of k))}
  (δ ε : Cor.mk X ⟶ Cor.mk Y) (x : X.left)
  (a : ∀ y : Y.left, (SmoothSite.nisnevichPointFiberCocone Y y ((toPresheaf k).obj P)).pt)

/-- Literal common-source and appended-target witnesses evaluate additively. -/
theorem fixed_tuple_correspondence_add
    (L : PointedGermLiftWitness k P δ x a) (M : PointedGermLiftWitness k P ε x a) :
    (L.add k P M).value k P = L.value k P + M.value k P :=
  PointedGermLiftWitness.value_add k P L M

/-- Negation changes the signed correspondence, not its target tuple. -/
theorem fixed_tuple_correspondence_neg (L : PointedGermLiftWitness k P δ x a) :
    (L.neg k P).value k P = -L.value k P :=
  PointedGermLiftWitness.value_neg k P L

/-- The empty witness evaluates to zero for every original germ tuple. -/
theorem fixed_tuple_correspondence_zero :
    (PointedGermLiftWitness.zero k P x a).value k P = 0 :=
  PointedGermLiftWitness.value_zero k P x a

open Lean in
run_cmd do
  for name in #[``fixed_tuple_correspondence_add, ``fixed_tuple_correspondence_neg,
      ``fixed_tuple_correspondence_zero, ``PointedGermLiftWitness.refine,
      ``PointedGermLiftWitness.value_refine, ``PointedGermLiftWitness.add,
      ``PointedGermLiftWitness.neg, ``PointedGermLiftWitness.zero] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual signed witness algebra at a fixed original germ tuple: standard foundations only."

end MotivicTest.PointedGermLiftCorrespondenceAlgebra
