/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightOne.Geometry.TorusNormRelation
public import Lean.Util.CollectAxioms

/-! # Direct audit of the actual identity-graph and ordinary reduced relation -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Motivic
open _root_.AlgebraicGeometry.PolynomialOpenQuotient.Laurent
open _root_.AlgebraicGeometry.Scheme.PolynomialLaurent
open _root_.AlgebraicGeometry.Scheme.SmoothSite
open _root_.Motivic.AffineTorusPolynomialPresentation
open Motivic.SmoothSiteTorusDivisor
open _root_.AlgebraicSimplex _root_.Motivic.PresheafWithTransfers

universe u

namespace MotivicTest.SmoothSiteTorusNormRelation

variable (k : Type u) [Field k]

theorem actual_original_relation :
    (toPresheaf k).map (torusIdentityAxis k 1 0) ≫ norm = 0 := norm_identityAxis

open Lean in
run_cmd do
  for name in #[``unitMorphism, ``linear_constant_isUnit, ``polynomialProjection_linear_isIso,
      ``polynomialInclusion_linear_target, ``polynomialCycle_linear_graph,
      ``affineStructureMorphism, ``unitMorphism_one, ``rationalDivisor_identityPoint_graph,
      ``cycleRationalFunction_identityGraph, ``signedValue_identityGraph,
      ``structureMorphism, ``graph_structureMorphism, ``baseCorrespondence_eq_zsmul,
      ``affineIso_structureMorphism, ``affineNorm_structureOne,
      ``affinePowerOneNorm_identityAxis, ``norm_identityAxis, ``actual_original_relation] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original identity-graph relation uses only standard Lean foundations."

end MotivicTest.SmoothSiteTorusNormRelation
