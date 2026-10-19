/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Diagonal.NormalizedEndpointCycles
public import Lean.Util.CollectAxioms

/-! Original graph endpoint cycles retain all normalized branches and lengths. -/

@[expose] public noncomputable section
open _root_.AlgebraicGeometry.Scheme (fundamentalCycle isNoetherian_of_finiteType)
open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory AlgebraicGeometry Motivic
open Motivic.DiagonalBoundarySupport
universe u
namespace MotivicTest.DiagonalNormalizedEndpointCycles
open _root_.AlgebraicGeometry.Scheme (IntegralCycle SmoothSite)
open _root_.AlgebraicGeometry.Scheme.Normalization
variable {k : Type u} [Field k] [CharZero k] {q : ℕ} (Z : Generator k q)

local instance normalizationFinite :
    IsFinite (FiniteCurve.normalizationMap (coordinateRing Z)) :=
  FiniteCurve.normalizationMap_isFinite (k := k) (coordinateRing Z)

local instance supportSpecNoetherian : IsNoetherian (Spec (.of (coordinateRing Z))) :=
  isNoetherian_of_finiteType (FiniteCurve.baseMap (k := k) (coordinateRing Z))

local instance normalizationSpecNoetherian :
    IsNoetherian (Spec (.of (FiniteCurve.ring (coordinateRing Z)))) :=
  isNoetherian_of_finiteType (FiniteCurve.normalizationMap (coordinateRing Z))

/-- This is the original endpoint correspondence, not a replacement evaluator. -/
theorem actual_endpoint_normalization (a : k) :
    (((Cor.graphFunctor k).map (WeightOneBoundaryNorm.evaluationPoint k a) ≫
      (show Cor.mk (_root_.AlgebraicSimplex.smoothSiteObj k 1) ⟶
        Cor.mk (SmoothSite.torusPower (.of k) q) from Z.cycle))).toIntegralCycle =
      IntegralCycle.finitePushforward (normalizedAffineFiberInclusion Z a)
        (fundamentalCycle (FiniteFlatCurve.fiber
          (FiniteAffineEndpointBranches.baseMap
            (FiniteCurve.ring (coordinateRing Z))) a)) :=
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
