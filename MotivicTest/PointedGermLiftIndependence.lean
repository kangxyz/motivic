/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Sheaf.Germs.Pointed.Evaluation.Additivity
public import Motivic.Transfers.Sheaf.Germs.Pointed.Lifts.Sections
public import Lean.Util.CollectAxioms

/-! Choice-independent additive generator evaluation on the original Nisnevich point fibers. -/
@[expose] public noncomputable section
open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory
open Opposite
open AlgebraicGeometry
open Motivic
open _root_.Motivic.PresheafWithTransfers
universe u
namespace MotivicTest.PointedGermLiftIndependence
variable (k : Type u) [Field k] (P : PresheafWithTransfers.{u + 1} k)
  (hP : Presheaf.IsSheaf (SmoothSite.nisnevichTopology (Spec (.of k))) ((toPresheaf k).obj P))
  {X Y : SmoothSite (Spec (.of k))}
include hP

/-- The original source-point value is independent of every actual finite witness. -/
theorem actual_finite_witness_independence (δ : Cor.mk X ⟶ Cor.mk Y) (x : X.left)
    (a : ∀ y : Y.left, (SmoothSite.nisnevichPointFiberCocone Y y ((toPresheaf k).obj P)).pt)
    (L M : PointedGermLiftWitness k P δ x a) : L.value k P = M.value k P :=
  PointedGermLiftWitness.value_eq k P hP L M

/-- The generator evaluator is genuinely additive on original germ tuples. -/
theorem actual_generator_additivity (A : FiniteCorrespondenceGenerator X.hom Y.hom)
    (x : X.left)
    (a b : ∀ y : Y.left, (SmoothSite.nisnevichPointFiberCocone Y y ((toPresheaf k).obj P)).pt) :
    generatorGermEvaluation k P A x (a + b) =
      generatorGermEvaluation k P A x a + generatorGermEvaluation k P A x b :=
  generatorGermEvaluation_add k P hP A x a b

open Lean in
run_cmd do
  for name in #[``actual_finite_witness_independence, ``actual_generator_additivity,
      ``generatorGermHom, ``generatorGermEvaluation_eq_of_witness,
      ``PointedGermLiftWitness.value_eq_transfer_of_restrictions] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original germ evaluation: choice independence and additivity, standard foundations only."

end MotivicTest.PointedGermLiftIndependence
