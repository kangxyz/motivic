/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightOne.Geometry.TorusGraphNorm
public import Lean.Util.CollectAxioms

/-! # Direct audit of canonical unit-graph normalization -/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory AlgebraicGeometry Motivic Opposite
open _root_.AlgebraicGeometry.PolynomialOpenQuotient.Laurent
open _root_.AlgebraicGeometry.Scheme.PolynomialLaurent
open _root_.AlgebraicGeometry.Scheme.SmoothSite
open _root_.Motivic.AffineTorusPolynomialPresentation
open Motivic.SmoothSiteTorusDivisor
open _root_.AlgebraicSimplex
open _root_.Motivic.PresheafWithTransfers
open Polynomial.BoundaryOneRationalFunctions

universe u

namespace MotivicTest.SmoothSiteTorusGraphNorm

variable {k : Type u} [Field k]

theorem actual_reduced_graph_normalization (X : SmoothSite (Spec (.of k)))
    [IsAffine X.left] [IsIntegral X.left] (u : (Γ(X.left, ⊤))ˣ) :
    reducedNorm.app (op X) ((toReducedTorus k 1).hom.app (op (Cor.mk X))
      (ULift.up ((Cor.graphFunctor k).map (affinePowerOneUnitMorphism X u)))) =
        ULift.up (Additive.ofMul u) := reducedNorm_unitGraph X u

open Lean in
run_cmd do
  for name in #[``unitPointFraction, ``fractionDegree_unitPoint, ``signedValueHom_unitPoint,
      ``rationalDivisor_unitPoint_graph, ``cycleRationalFunction_unitGraph,
      ``signedValue_unitGraph, ``affineUnitMorphism, ``affineNorm_unitGraph,
      ``affinePowerOneUnitMorphism, ``affinePowerOneNorm_unitGraph,
      ``reducedNorm_unitGraph, ``actual_reduced_graph_normalization] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Canonical original unit-graph normalization uses only standard Lean foundations."

end MotivicTest.SmoothSiteTorusGraphNorm
