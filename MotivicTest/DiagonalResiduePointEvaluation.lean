/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Diagonal.ResiduePointEvaluation
public import Lean.Util.CollectAxioms

/-! Actual residue fields and full nonreduced finite cycles, in every weight. -/

@[expose] public noncomputable section
open _root_.AlgebraicGeometry.Scheme (fundamentalCycle)
open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open Motivic.DiagonalPointNorm Motivic.DiagonalResiduePointEvaluation
open scoped BigOperators

universe u
namespace MotivicTest.DiagonalResiduePointEvaluation
open _root_.AlgebraicGeometry.Scheme (IntegralCycle SmoothSite)
variable {k : Type u} [Field k] [CharZero k] {T : Scheme.{u}} [IsNoetherian T]
  {q : ℕ}

/-- The original full finite cycle retains every actual residue norm and multiplicity. -/
theorem actual_full_residue_sum
    (p : T ⟶ Spec (.of k)) [IsFinite p]
    (j : T ⟶ DiagonalFinitePointEvaluation.ambient k q) [IsFinite j]
    (hp : j ≫ pullback.fst (SmoothSite.base (Spec (.of k))).hom
      (SmoothSite.torusPower (.of k) q).hom = p)
    (α : WeightOnePointNorm.point k ⟶ DiagonalCycleSymbols.target k q)
    (hα : FiniteCorrespondence.toIntegralCycle α =
      IntegralCycle.finitePushforward j (fundamentalCycle T)) :
    let : Fintype T := finiteSchemeFintype p
    cycleValue k q α = ∑ x : T,
      (IntegralCycle.toPoints (fundamentalCycle T) x) •
        residueValue p (DiagonalFiniteFundamentalEvaluation.schemeCoordinateUnit j) x :=
  cycleValue_eq_residue_sum_of_finite p j hp α hα

open Lean in
run_cmd do
  for name in #[``actual_full_residue_sum, ``residue_projection,
      ``residue_coordinate, ``residueFinite, ``residue_fundamental,
      ``fundamental_eq_residue_sum, ``cycleValue_eq_residue_sum_of_finite] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual full residue norms and local multiplicities: standard foundations only."
end MotivicTest.DiagonalResiduePointEvaluation
