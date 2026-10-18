/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.WeightTwoMilnorNormComparison
public import Motivic.Cohomology.Motivic.WeightTwoPointPresentation

/-!
# Surjectivity of the original weight-two Milnor symbols

Each actual finite point is presented using its whole joint coordinate field.
The constructed polynomial Milnor norm then supplies a preimage of its two-unit
transfer. Signed finite sums give every original raw class, and the actual
field-evaluation comparison and coefficient reduction give the derived and
finite statements. The cycle preimage below is not asserted to annihilate
boundaries, so no inverse, injectivity, or presentation independence is claimed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial

universe w u

namespace Motivic.WeightTwoMilnorSurjective

open MilnorK.K2 MilnorK.K3.PolynomialNorm
open WeightTwoMilnorSymbol WeightTwoMilnorNormComparison

variable (k : Type u) [Field k] [CharZero k]

/-- A literal Milnor preimage of a signed point cycle, before quotienting by boundaries. -/
def cyclePreimage (α : WeightOnePointNorm.point k ⟶ WeightTwoSymbols.target k) :
    MilnorK.K2.Group k :=
  α.sum fun Z n => n • polynomialNorm (WeightTwoPointPresentation.polynomial Z)
    (symbol (WeightTwoPointPresentation.polynomialUnit Z 0)
      (WeightTwoPointPresentation.polynomialUnit Z 1))

/-- The actual symbol of this signed preimage is the original raw cycle class. -/
theorem rawMilnorSymbol_cyclePreimage
    (α : WeightOnePointNorm.point k ⟶ WeightTwoSymbols.target k) :
    rawMilnorSymbol k (cyclePreimage k α) = WeightTwoSymbols.cycleClass k α := by
  classical
  rw [cyclePreimage, map_finsuppSum, WeightTwoPointPresentation.cycleClass_eq_sum_corestriction]
  apply Finset.sum_congr rfl
  intro Z _
  dsimp only
  rw [map_zsmul, raw_norm, rawMilnorSymbol_symbol]

/-- Every original raw H22 class has an actual Milnor K2 preimage. -/
theorem rawMilnorSymbol_surjective : Function.Surjective (rawMilnorSymbol k) := by
  intro x
  obtain ⟨α, rfl⟩ := WeightTwoSymbols.cycleClass_surjective k x
  exact ⟨cyclePreimage k α, rawMilnorSymbol_cyclePreimage k α⟩

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Surjectivity in the originally defined derived integral motivic group. -/
theorem motivicMilnorSymbol_surjective : Function.Surjective (motivicMilnorSymbol k) := by
  intro x
  obtain ⟨y, hy⟩ := rawMilnorSymbol_surjective k
    (motivicRawBaseEvaluationComparison k 2 2 x)
  refine ⟨y, ?_⟩
  apply (motivicRawBaseEvaluationComparison k 2 2).injective
  rw [motivicMilnorSymbol_comparison, hy]

/-- Every natural coefficient level uses the actual derived coefficient reduction. -/
theorem finiteMilnorSymbol_surjective (n : ℕ) :
    Function.Surjective (finiteMilnorSymbol k n) := by
  intro x
  obtain ⟨y, rfl⟩ := FieldTopDegree.integralReduction_surjective k 2 n x
  obtain ⟨z, rfl⟩ := motivicMilnorSymbol_surjective k y
  exact ⟨z, rfl⟩

/-- The original map from Milnor K2 modulo n is surjective for every natural n. -/
theorem finiteMilnorSymbolModulo_surjective (n : ℕ) :
    Function.Surjective (finiteMilnorSymbolModulo k n) := by
  intro x
  obtain ⟨y, rfl⟩ := finiteMilnorSymbol_surjective k n x
  exact ⟨QuotientAddGroup.mk y, rfl⟩

end Motivic.WeightTwoMilnorSurjective
