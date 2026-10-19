/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Sheaf.Germs.Pointed.Lifts.Evaluation
public import Lean.Util.CollectAxioms

/-! Existence of actual generator evaluation witnesses for original arbitrary-point germs. -/
@[expose] public noncomputable section
open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory
open Opposite
open AlgebraicGeometry
open Motivic
open _root_.Motivic.PresheafWithTransfers
universe u
namespace MotivicTest.PointedGermLiftEvaluation
variable (k : Type u) [Field k] (P : PresheafWithTransfers.{u + 1} k)
  {X Y : SmoothSite (Spec (.of k))}

/-- The witness contains the actual original graph factorization and original germ tuple. -/
theorem actual_generator_witness (A : FiniteCorrespondenceGenerator X.hom Y.hom)
    (x : X.left) (a : ∀ y : Y.left,
      (SmoothSite.nisnevichPointFiberCocone Y y ((toPresheaf k).obj P)).pt) :
    Nonempty (PointedGermLiftWitness k P (show Cor.mk X ⟶ Cor.mk Y from A.cycle) x a) :=
  exists_pointedGermLiftWitness k P A x a

open Lean in
run_cmd do
  for name in #[``actual_generator_witness, ``PointedGermLiftWitness.value] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual generator lift witnesses: standard foundations only."

end MotivicTest.PointedGermLiftEvaluation
