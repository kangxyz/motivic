/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightTwo.Corestriction
public import Lean.Util.CollectAxioms

/-!
# Consumers of literal finite-extension cycle transfer

The original signed correspondence groups and identity-axis cokernels are used
in both singular degrees. No separability or smoothness of the extension is assumed.
This test does not assert boundary preservation or homology corestriction.
-/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (IntegralCycle)
open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Motivic
open WeightTwoCorestriction _root_.AlgebraicSimplex _root_.Motivic.PresheafWithTransfers

universe u

namespace MotivicTest.WeightTwoCorestriction

variable {k E : Type u} [Field k] [Field E] [Algebra k E] [Module.Finite k E]

/-- Degree zero is the actual finite pushforward on integral cycles. -/
theorem actual_degree_zero
    (α : Cor.simplexProduct (WeightOnePointNorm.point E) 0 ⟶ WeightTwoSymbols.target E) :
    FiniteCorrespondence.toIntegralCycle (cyclePushforward (k := k) 0 2 α) =
      IntegralCycle.finitePushforward (ambientMap (k := k) (E := E) 0 2)
        (FiniteCorrespondence.toIntegralCycle α) :=
  toIntegralCycle_cyclePushforward 0 2 α

/-- Degree one has the same full signed finite pushforward. -/
theorem actual_degree_one
    (α : Cor.simplexProduct (WeightOnePointNorm.point E) 1 ⟶ WeightTwoSymbols.target E) :
    FiniteCorrespondence.toIntegralCycle (cyclePushforward (k := k) 1 2 α) =
      IntegralCycle.finitePushforward (ambientMap (k := k) (E := E) 1 2)
        (FiniteCorrespondence.toIntegralCycle α) :=
  toIntegralCycle_cyclePushforward 1 2 α

/-- Coincident images add their signed original residue-degree coefficients. -/
theorem colliding_images (r : ℕ)
    (A B : FiniteCorrespondenceGenerator (source E r).hom (target E 2).hom)
    (h : imageGenerator (k := k) r 2 A = imageGenerator (k := k) r 2 B)
    (n m : ℤ) :
    cyclePushforward (k := k) r 2 (Finsupp.single A n + Finsupp.single B m) =
      Finsupp.single (imageGenerator (k := k) r 2 A)
        (n * ((ambientMap (k := k) (E := E) r 2).residueDegree A.point : ℤ) +
         m * ((ambientMap (k := k) (E := E) r 2).residueDegree B.point : ℤ)) := by
  rw [map_add, cyclePushforward_single, cyclePushforward_single, ← h, Finsupp.single_add]

/-- Both identity axes commute with the same actual pushforward. -/
theorem actual_axis (r : ℕ) (i : Fin 2)
    (α : Cor.mk (source E r) ⟶ Cor.mk (target E 1)) :
    cyclePushforward (k := k) r 2
      (α ≫ (Cor.graphFunctor E).map (SmoothSite.torusInsertOne (.of E) 1 i)) =
      cyclePushforward (k := k) r 1 α ≫
        (Cor.graphFunctor k).map (SmoothSite.torusInsertOne (.of k) 1 i) :=
  cyclePushforward_axis r 1 i α

/-- Actual quotient sections retain their represented cycles after descent. -/
theorem actual_quotient (r : ℕ)
    (α : Cor.mk (source E r) ⟶ Cor.mk (target E 2)) :
    reducedPushforward (k := k) (E := E) r 2
      ((toReducedTorus E 2).hom.app (op (Cor.mk (source E r))) (ULift.up α)) =
      (toReducedTorus k 2).hom.app (op (Cor.mk (source k r)))
        (ULift.up (cyclePushforward (k := k) r 2 α)) :=
  reducedPushforward_quotient r 2 α

open Lean in
run_cmd do
  for name in #[``ambientMap_isFinite, ``sourceMap_surjective, ``imageGenerator,
      ``cyclePushforward, ``cyclePushforward_single, ``toIntegralCycle_cyclePushforward,
      ``ambientMap_axis, ``toIntegralCycle_axis, ``cyclePushforward_axis,
      ``liftedCyclePushforward_relations, ``reducedPushforward, ``reducedPushforward_quotient,
      ``actual_degree_zero, ``actual_degree_one, ``colliding_images,
      ``actual_axis, ``actual_quotient] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Finite cycle transfer and actual identity-axis descent use only standard foundations."

end MotivicTest.WeightTwoCorestriction
