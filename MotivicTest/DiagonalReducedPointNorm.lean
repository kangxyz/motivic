/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Diagonal.ReducedPointNorm
public import Aglib.KTheory.MilnorK.Dedekind.StalkResidue
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.MilnorK.NormalizedAffineEndpointNorm
public import Lean.Util.CollectAxioms

/-! Actual reduced quotient evaluation and original local/normalization audit. -/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Motivic Opposite
open _root_.AlgebraicSimplex _root_.Motivic.PresheafWithTransfers Motivic.DiagonalReducedPointNorm

universe u
namespace MotivicTest.DiagonalReducedPointNorm
variable (k : Type u) [Field k] [CharZero k]

/-- The original reduced quotient, not a substitute group, recovers each rational symbol. -/
theorem actual_reduced_rational_tuple (q : ℕ) (a : Fin q → kˣ) :
    reducedNorm k q ((toReducedTorus k q).hom.app (op (WeightOnePointNorm.point k))
      (ULift.up ((Cor.graphFunctor k).map (DiagonalCycleSymbols.rationalTuple k q a)))) =
        MilnorK.symbol a :=
  reducedNorm_rationalTuple q a

open Lean in
run_cmd do
  for name in #[``actual_reduced_rational_tuple, ``largeCycleNorm,
      ``relation_largeCycleNorm, ``reducedNormLarge, ``toReducedTorus_reducedNormLarge,
      ``reducedNorm, ``reducedNorm_quotient, ``reducedNorm_rationalTuple,
      ``MilnorK.DedekindStalkResidue.residue_eq,
      ``_root_.AlgebraicGeometry.FiniteCurveNormalization.normalized_endpoint_sum_eq] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual reduced quotient and original normalization maps: standard foundations only."

end MotivicTest.DiagonalReducedPointNorm
