/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.WeightTwoSkewSymmetry
public import Mathlib.Algebra.Field.ZMod
public import Lean.Util.CollectAxioms

/-!
# Consumers of genuine skew-symmetric weight-two symbols

The original quadratic family supplies skew symmetry. These consumers retain
raw and actual derived graph classes, including repeated coordinates and
characteristic-dividing coefficient levels. They do not assert alternation.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Motivic
open Motivic.WeightTwoSymbols Motivic.WeightTwoFiniteSymbols
open Motivic.WeightTwoSkewSymmetry
open scoped TensorProduct

universe w u

namespace MotivicTest.WeightTwoSkewSymmetry

variable (k : Type u) [Field k]

/-- The quadratic diagonal relation uses the actual graph classes. -/
theorem original_diagonal (a b : kˣ) :
    graphSymbol k (a * b) (a * b) = graphSymbol k a a + graphSymbol k b b :=
  graphSymbol_diagonal_mul k a b

/-- Swapping the original coordinates gives the actual negative class. -/
theorem original_swap (a b : kˣ) : graphSymbol k b a = -graphSymbol k a b :=
  graphSymbol_swap k a b

/-- A repeated coordinate remains only two-torsion at this stage. -/
theorem repeated_coordinate (a : kˣ) : 2 • graphSymbol k a a = 0 :=
  two_nsmul_graphSymbol_diagonal k a

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The actual derived integral tensor retains the same sign. -/
theorem integral_swap (a b : kˣ) :
    motivicTensorSymbol k (Additive.ofMul a ⊗ₜ[ℤ] Additive.ofMul b) +
      motivicTensorSymbol k (Additive.ofMul b ⊗ₜ[ℤ] Additive.ofMul a) = 0 :=
  motivicTensorSymbol_add_swap k a b

/-- The original finite reduction preserves this relation at composite level six. -/
theorem finite_six (a b : kˣ) :
    finiteTensorSymbol k 6 (Additive.ofMul a ⊗ₜ[ℤ] Additive.ofMul b) +
      finiteTensorSymbol k 6 (Additive.ofMul b ⊗ₜ[ℤ] Additive.ofMul a) = 0 :=
  finiteTensorSymbol_add_swap k 6 a b

/-- Characteristic two does not change the raw relation or divide by two. -/
theorem characteristic_two (a : (ZMod 2)ˣ) :
    2 • graphSymbol (ZMod 2) a a = 0 :=
  two_nsmul_graphSymbol_diagonal (ZMod 2) a

open Lean in
run_cmd do
  for name in #[``diagonalTorus, ``rationalPoint_diagonalTorus,
      ``graphSymbol_diagonal_mul, ``graphSymbol_add_swap, ``graphSymbol_swap,
      ``two_nsmul_graphSymbol_diagonal, ``motivicTensorSymbol_add_swap,
      ``finiteTensorSymbol_add_swap, ``original_diagonal, ``original_swap,
      ``repeated_coordinate, ``integral_swap, ``finite_six, ``characteristic_two] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual weight-two skew symmetry uses only standard Lean foundations."

end MotivicTest.WeightTwoSkewSymmetry
