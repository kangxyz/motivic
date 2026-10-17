/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.DiagonalCorestriction
public import Lean.Util.CollectAxioms

/-!
# Consumers of actual all-weight diagonal corestriction

These tests exercise the literal endpoint boundary, the actual finite-point
fundamental cycle, and the original raw and derived groups over arbitrary
finite field extensions. No separability or characteristic-zero hypothesis is
introduced. The consumer rejects every nonstandard axiom recursively.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Motivic Motivic.DiagonalTopDegree Motivic.DiagonalCycleSymbols
open Motivic.DiagonalCorestriction

universe w u

namespace MotivicTest.DiagonalCorestriction

variable {k E : Type u} [Field k] [Field E] [Algebra k E] [Module.Finite k E]

/-- The transferred full endpoint difference still vanishes in the original raw homology. -/
theorem actual_boundary_zero (q : ℕ) (x : chains E q 1) :
    singularClass k q (WeightTwoCorestriction.reducedPushforward (k := k) (E := E) 0 q
      (boundary E q x)) = 0 := by
  rw [reducedPushforward_boundary, singularClass_boundary]

/-- Weight zero uses the same genuine singular boundary quotient. -/
theorem actual_weight_zero_boundary (x : chains E 0 1) :
    singularClass k 0 (WeightTwoCorestriction.reducedPushforward (k := k) (E := E) 0 0
      (boundary E 0 x)) = 0 := actual_boundary_zero 0 x

/-- Odd weight retains the signed endpoint difference, including its negative. -/
theorem actual_odd_weight_boundary (x : chains E 3 1) :
    corestriction (k := k) 3 (singularClass E 3 (-boundary E 3 x)) = 0 := by
  rw [corestriction_singularClass, map_neg, map_neg,
    reducedPushforward_boundary, singularClass_boundary, neg_zero]

/-- The original weight-two corestriction is recovered on each original raw class. -/
theorem actual_weight_two_agreement (x : (motivicRawBaseComplex E 2).homology 2) :
    corestriction (k := k) 2 x = WeightTwoCorestriction.corestriction (k := k) x :=
  DFunLike.congr_fun (corestriction_two (k := k) (E := E)) x

/-- A signed sum of actual point cycles retains its signs through original raw corestriction. -/
theorem actual_signed_cycle_transfer (q : ℕ) (α β : point E ⟶ target E q) (n : ℤ) :
    corestriction (k := k) q (cycleClass E q (n • α - β)) =
      n • cycleClass k q (pointPushforward (k := k) q α) -
        cycleClass k q (pointPushforward (k := k) q β) := by
  rw [corestriction_cycleClass, map_sub, map_zsmul, map_sub, map_zsmul]

/-- The actual whole finite point, rather than an unweighted image, is the graph representative. -/
theorem actual_graph_fundamental_cycle (q : ℕ) (a : Fin q → Eˣ) :
    FiniteCorrespondence.toIntegralCycle
      (f := (SmoothSite.base (Spec (.of k))).hom)
      (g := (SmoothSite.torusPower (.of k) q).hom)
      (pointPushforward (k := k) q ((Cor.graphFunctor E).map (rationalTuple E q a))) =
    IntegralCycle.finitePushforward (finitePointMap (k := k) q (rationalTuple E q a))
      (fundamentalCycle (Spec (.of E))) :=
  toIntegralCycle_pointPushforward_graph q _

variable [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of E))) AddCommGrpCat.{u + 1})]

/-- The graph-symbol formula lives in the originally defined derived group on each field. -/
theorem actual_derived_graph_transfer (q : ℕ) (a : Fin q → Eˣ) :
    motivicCorestriction (k := k) q
      ((motivicRawBaseEvaluationComparison E q q).symm (graphSymbol E q a)) =
    (motivicRawBaseEvaluationComparison k q q).symm
      (cycleClass k q (pointPushforward (k := k) q
        ((Cor.graphFunctor E).map (rationalTuple E q a)))) :=
  motivicCorestriction_cycleClass q _

open Lean in
run_cmd do
  for name in #[``reducedPushforward_face, ``reducedPushforward_boundary,
      ``quotientCorestriction, ``quotientCorestriction_mk, ``corestriction,
      ``corestriction_singularClass, ``corestriction_cycleClass, ``corestriction_unique,
      ``corestriction_two, ``corestriction_graphSymbol, ``finitePointMap_fst,
      ``finitePointMap_snd, ``toIntegralCycle_pointPushforward_graph,
      ``motivicCorestriction, ``motivicCorestriction_comparison,
      ``motivicCorestriction_cycleClass, ``actual_boundary_zero,
      ``actual_weight_zero_boundary, ``actual_odd_weight_boundary,
      ``actual_weight_two_agreement, ``actual_signed_cycle_transfer,
      ``actual_graph_fundamental_cycle,
      ``actual_derived_graph_transfer] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual all-weight corestriction uses only standard foundations."

end MotivicTest.DiagonalCorestriction
