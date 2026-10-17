/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.WeightOneSplitPolynomialCycle
public import Lean.Util.CollectAxioms

/-!
# Consumers of actual split polynomial cycles

These equalities concern the full actual finite correspondences. Repeated roots
are counted with their original local lengths, with no characteristic or
separability restriction.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial
open Motivic Motivic.WeightOnePointNorm Motivic.WeightOneInterpolationCycle
open Motivic.WeightOneSplitPolynomialCycle

universe u

namespace MotivicTest.WeightOneSplitPolynomialCycle

variable {k : Type u} [Field k]

/-- The actual unreduced split quotient gives the prescribed graph cycle. -/
theorem full_split_correspondence (a : kˣ) (m : ℕ) :
    polynomialCycle ((X - C 1) ^ m * (X - C (a : k)))
      (split_monic a m) (split_coeff_zero_ne_zero a m) =
        (Cor.graphFunctor k).map (rationalPoint k a) +
          (m : ℤ) • (Cor.graphFunctor k).map (rationalPoint k 1) :=
  polynomialCycle_split a m

/-- Coalescing the norm and identity roots retains every nilpotent multiplicity. -/
theorem coalesced_roots (m : ℕ) :
    polynomialCycle (((X - C 1) ^ m * (X - C 1)) : k[X])
      (split_monic (1 : kˣ) m) (split_coeff_zero_ne_zero (1 : kˣ) m) =
        ((m + 1 : ℕ) : ℤ) • (Cor.graphFunctor k).map (rationalPoint k 1) :=
  polynomialCycle_split_one m

/-- The interpolation endpoint equality is an equality before either quotient. -/
theorem norm_endpoint (p : k[X]) (hd : 1 ≤ p.natDegree) (h0 : p.coeff 0 ≠ 0) :
    polynomialCycle (MonicUnitInterpolation.target p) (MonicUnitInterpolation.target_monic p)
      ((MonicUnitInterpolation.target_coeff_zero p hd).trans_ne h0) =
        (Cor.graphFunctor k).map (rationalPoint k
          (Units.mk0 (MonicUnitInterpolation.normValue p)
            (MonicUnitInterpolation.normValue_ne_zero p h0))) +
        ((p.natDegree - 1 : ℕ) : ℤ) •
          (Cor.graphFunctor k).map (rationalPoint k 1) :=
  polynomialCycle_target p hd h0

/-- Forgetting admissibility still gives the same entire split fundamental pushforward. -/
theorem full_split_fundamental_cycle (a : kˣ) (m : ℕ) :
    IntegralCycle.finitePushforward
      (polynomialInclusion ((X - C 1) ^ m * (X - C (a : k))) (split_coeff_zero_ne_zero a m))
      (fundamentalCycle (Spec (.of (AdjoinRoot ((X - C 1) ^ m * (X - C (a : k))))))) =
        FiniteCorrespondence.toIntegralCycle
          ((Cor.graphFunctor k).map (rationalPoint k a) +
            (m : ℤ) • (Cor.graphFunctor k).map (rationalPoint k 1)) := by
  exact (toIntegralCycle_polynomialCycle _ (split_monic a m)
    (split_coeff_zero_ne_zero a m)).symm.trans
      (congrArg FiniteCorrespondence.toIntegralCycle (polynomialCycle_split a m))

/-- Arbitrary unit roots give the sum of their two actual graph correspondences. -/
theorem actual_quadratic_graph_sum (a b : kˣ) :
    polynomialCycle ((X - C (a : k)) * (X - C (b : k)))
      (twoLinear_monic a b) (twoLinear_coeff_zero_ne_zero a b) =
        (Cor.graphFunctor k).map (rationalPoint k a) +
          (Cor.graphFunctor k).map (rationalPoint k b) :=
  polynomialCycle_twoLinear a b

/-- The doubled arbitrary unit retains its nonreduced multiplicity. -/
theorem actual_quadratic_double_root (a : kˣ) :
    polynomialCycle ((X - C (a : k)) * (X - C (a : k)))
      (twoLinear_monic a a) (twoLinear_coeff_zero_ne_zero a a) =
        (2 : ℤ) • (Cor.graphFunctor k).map (rationalPoint k a) := by
  simpa only [two_zsmul] using polynomialCycle_twoLinear a a

/-- The actual quadratic used for multiplicativity has the original unit product as norm. -/
theorem actual_quadratic_norm_value (a b : kˣ) :
    MonicUnitInterpolation.normValue ((X - C (a : k)) * (X - C (b : k))) =
      (a : k) * (b : k) :=
  twoLinear_normValue a b

end MotivicTest.WeightOneSplitPolynomialCycle

open Lean in
run_cmd do
  for name in #[
      `Motivic.WeightOneSplitPolynomialCycle.polynomialBranchGenerator_eq_graph,
      `Motivic.WeightOneSplitPolynomialCycle.quotient_scalar_surjective,
      `Motivic.WeightOneSplitPolynomialCycle.sum_local_length_eq_natDegree,
      `Motivic.WeightOneSplitPolynomialCycle.maximal_eq_of_root_eq,
      `Motivic.WeightOneSplitPolynomialCycle.scalarMaximal,
      `Motivic.WeightOneSplitPolynomialCycle.scalarMaximal_root,
      `Motivic.WeightOneSplitPolynomialCycle.split_residual_root,
      `Motivic.WeightOneSplitPolynomialCycle.polynomialCycle_eq_sum_graph,
      `Motivic.WeightOneSplitPolynomialCycle.polynomialCycle_eq_degree_smul_graph,
      `Motivic.WeightOneSplitPolynomialCycle.polynomialCycle_split_one,
      `Motivic.WeightOneSplitPolynomialCycle.polynomialCycle_split_of_local_length,
      `Motivic.WeightOneSplitPolynomialCycle.polynomialCycle_split,
      `Motivic.WeightOneSplitPolynomialCycle.polynomialCycle_target,
      `Motivic.WeightOneSplitPolynomialCycle.twoLinear_monic,
      `Motivic.WeightOneSplitPolynomialCycle.twoLinear_coeff_zero,
      `Motivic.WeightOneSplitPolynomialCycle.twoLinear_coeff_zero_ne_zero,
      `Motivic.WeightOneSplitPolynomialCycle.twoLinear_natDegree,
      `Motivic.WeightOneSplitPolynomialCycle.twoLinear_normValue,
      `Motivic.WeightOneSplitPolynomialCycle.twoLinear_residual_root,
      `Motivic.WeightOneSplitPolynomialCycle.twoLinear_simple_local_length,
      `Motivic.WeightOneSplitPolynomialCycle.polynomialCycle_twoRoots_of_local_length,
      `Motivic.WeightOneSplitPolynomialCycle.polynomialCycle_twoLinear,
      `MotivicTest.WeightOneSplitPolynomialCycle.full_split_correspondence,
      `MotivicTest.WeightOneSplitPolynomialCycle.coalesced_roots,
      `MotivicTest.WeightOneSplitPolynomialCycle.norm_endpoint,
      `MotivicTest.WeightOneSplitPolynomialCycle.full_split_fundamental_cycle,
      `MotivicTest.WeightOneSplitPolynomialCycle.actual_quadratic_graph_sum,
      `MotivicTest.WeightOneSplitPolynomialCycle.actual_quadratic_double_root,
      `MotivicTest.WeightOneSplitPolynomialCycle.actual_quadratic_norm_value] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual split polynomial cycles use only standard Lean foundations."
