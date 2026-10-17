/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.DiagonalNormalizedEndpointCycles
public import Lean.Util.CollectAxioms

/-! Original graph endpoint cycles retain all normalized branches and lengths. -/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Motivic
open Motivic.DiagonalBoundarySupport
universe u
namespace MotivicTest.DiagonalNormalizedEndpointCycles
variable {k : Type u} [Field k] [CharZero k] {q : ℕ} (Z : Generator k q)

local instance normalizationFinite :
    IsFinite (FiniteCurveNormalization.normalizationMap (coordinateRing Z)) :=
  FiniteCurveNormalization.normalizationMap_isFinite (k := k) (coordinateRing Z)

local instance supportSpecNoetherian : IsNoetherian (Spec (.of (coordinateRing Z))) :=
  isNoetherian_of_finiteType (FiniteCurveNormalization.baseMap (k := k) (coordinateRing Z))

local instance normalizationSpecNoetherian :
    IsNoetherian (Spec (.of (FiniteCurveNormalization.ring (coordinateRing Z)))) :=
  isNoetherian_of_finiteType (FiniteCurveNormalization.normalizationMap (coordinateRing Z))

/-- This is the original endpoint correspondence, not a replacement evaluator. -/
theorem actual_endpoint_normalization (a : k) :
    (((Cor.graphFunctor k).map (WeightOneBoundaryNorm.evaluationPoint k a) ≫
      (show Cor.mk (AlgebraicSimplex.smoothSiteObj k 1) ⟶
        Cor.mk (SmoothSite.torusPower (.of k) q) from Z.cycle))).toIntegralCycle =
      IntegralCycle.finitePushforward (normalizedAffineFiberInclusion Z a)
        (fundamentalCycle (FiniteFlatCurve.fiber
          (FiniteAffineEndpointBranches.baseMap
            (FiniteCurveNormalization.ring (coordinateRing Z))) a)) :=
  toIntegralCycle_endpoint_normalizedAffine Z a

open Lean in
run_cmd do
  for name in #[``actual_endpoint_normalization,
      ``normalizedFiberMap_fundamentalCycle, ``toIntegralCycle_endpoint_normalized,
      ``normalizedFiberMap_support, ``toIntegralCycle_endpoint_normalizedAffine,
      ``normalizedAffineFiberIso_support, ``normalizedAffineFiberInclusion_fst] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual normalized endpoint diagrams: standard foundations only."

end MotivicTest.DiagonalNormalizedEndpointCycles
