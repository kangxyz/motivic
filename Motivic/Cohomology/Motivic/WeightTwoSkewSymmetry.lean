/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.WeightTwoFiniteSymbols

/-!
# Skew symmetry of genuine weight-two graph symbols

The diagonal postcomposition of the original finite-flat quadratic family
makes the diagonal graph class multiplicative. Together with the proved
bilinearity, this gives skew symmetry. The diagonal is only proved to be
2-torsion; no alternating or Steinberg relation is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

universe w u

namespace Motivic.WeightTwoSkewSymmetry

open WeightOnePointNorm WeightTwoSymbols WeightTwoFiniteSymbols

variable (k : Type u) [Field k]

/-- Repeat the original one-fold torus coordinate, using the literal product. -/
def diagonalTorus : SmoothSite.torusPower (.of k) 1 ⟶
    SmoothSite.torusPower (.of k) 2 :=
  SmoothSite.torusPowerLift (.of k) 2
    (fun _ => SmoothSite.torusCoordinate (.of k) 1 0)

/-- The diagonal retains both coordinates of each original rational point. -/
@[reassoc (attr := simp)]
theorem rationalPoint_diagonalTorus (a : kˣ) :
    rationalPoint k a ≫ diagonalTorus k = rationalPair k a a := by
  apply SmoothSite.torusPower_hom_ext
  intro i
  rw [Category.assoc, diagonalTorus, rationalPair,
    SmoothSite.torusPowerLift_coordinate, SmoothSite.torusPowerLift_coordinate]
  fin_cases i <;> exact SmoothSite.torusPowerLift_coordinate (.of k) 1 _ 0

/-- The full quadratic endpoint relation gives additivity of the diagonal class. -/
theorem graphSymbol_diagonal_mul (a b : kˣ) :
    graphSymbol k (a * b) (a * b) = graphSymbol k a a + graphSymbol k b b := by
  have h := cycleClass_quadratic_postcompose k a b (diagonalTorus k)
  simp only [rationalPoint_diagonalTorus] at h
  change graphSymbol k a a + graphSymbol k b b =
    graphSymbol k (a * b) (a * b) + graphSymbol k 1 1 at h
  simpa only [graphSymbol_one_left, add_zero] using h.symm

/-- The actual raw graph symbols are skew-symmetric in every characteristic. -/
theorem graphSymbol_add_swap (a b : kˣ) :
    graphSymbol k a b + graphSymbol k b a = 0 := by
  have h := graphSymbol_diagonal_mul k a b
  rw [graphSymbol_mul_left, graphSymbol_mul_right, graphSymbol_mul_right] at h
  have hs : (graphSymbol k a a + graphSymbol k b b) +
      (graphSymbol k a b + graphSymbol k b a) =
        (graphSymbol k a a + graphSymbol k b b) + 0 := by
    calc
      _ = (graphSymbol k a a + graphSymbol k a b) +
          (graphSymbol k b a + graphSymbol k b b) := by abel
      _ = _ := by simpa only [add_zero] using h
  exact add_left_cancel hs

/-- Swapping the two genuine rational coordinates negates their raw class. -/
theorem graphSymbol_swap (a b : kˣ) : graphSymbol k b a = -graphSymbol k a b :=
  eq_neg_of_add_eq_zero_left (graphSymbol_add_swap k b a)

/-- A repeated-coordinate graph class is annihilated by two, without division by two. -/
theorem two_nsmul_graphSymbol_diagonal (a : kˣ) : 2 • graphSymbol k a a = 0 := by
  simpa only [two_nsmul] using graphSymbol_add_swap k a a

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The integral derived tensor symbol retains the geometric skew relation. -/
theorem motivicTensorSymbol_add_swap (a b : kˣ) :
    motivicTensorSymbol k (Additive.ofMul a ⊗ₜ[ℤ] Additive.ofMul b) +
      motivicTensorSymbol k (Additive.ofMul b ⊗ₜ[ℤ] Additive.ofMul a) = 0 := by
  apply (motivicRawBaseEvaluationComparison k 2 2).injective
  simpa only [map_add, map_zero, motivicTensorSymbol_tmul_comparison] using
    graphSymbol_add_swap k a b

/-- The original finite reduction preserves skew symmetry at every level. -/
theorem finiteTensorSymbol_add_swap (n : ℕ) (a b : kˣ) :
    finiteTensorSymbol k n (Additive.ofMul a ⊗ₜ[ℤ] Additive.ofMul b) +
      finiteTensorSymbol k n (Additive.ofMul b ⊗ₜ[ℤ] Additive.ofMul a) = 0 := by
  simpa only [map_add, map_zero, finiteTensorSymbol_eq_reduction] using
    congrArg (motivicBaseIntegralReduction k 2 2 n) (motivicTensorSymbol_add_swap k a b)

end Motivic.WeightTwoSkewSymmetry
