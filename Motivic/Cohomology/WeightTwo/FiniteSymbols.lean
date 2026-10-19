/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightTwo.Symbols

/-!
# Genuine weight-two symbols with finite coefficients

The bilinear rational-point tensor symbol is reduced by the original integral
coefficient map into actual derived finite motivic cohomology. Its cone and
top-degree quotient comparisons retain the integral symbol exactly. Every
value is annihilated by the coefficient level, including composite levels and
levels divisible by the characteristic. No Steinberg descent or Milnor
K-theory comparison is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

universe w u

namespace Motivic.WeightTwoFiniteSymbols
open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k]
variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The original coefficient reduction of the genuine integral weight-two symbol. -/
def finiteTensorSymbol (n : ℕ) : (Additive kˣ ⊗[ℤ] Additive kˣ) →+
    motivicFiniteCohomology k 2 2 n (SmoothSite.base (Spec (.of k))) :=
  (motivicBaseIntegralReduction k 2 2 n).comp (WeightTwoSymbols.motivicTensorSymbol k)

/-- The finite symbol uses the original integral reduction without a new comparison map. -/
theorem finiteTensorSymbol_eq_reduction (n : ℕ) (x : Additive kˣ ⊗[ℤ] Additive kˣ) :
    finiteTensorSymbol k n x =
      motivicBaseIntegralReduction k 2 2 n (WeightTwoSymbols.motivicTensorSymbol k x) := rfl

/-- A tensor generator reduces the original rational graph class. -/
theorem finiteTensorSymbol_tmul (n : ℕ) (a b : kˣ) :
    finiteTensorSymbol k n (Additive.ofMul a ⊗ₜ[ℤ] Additive.ofMul b) =
      motivicBaseIntegralReduction k 2 2 n
        ((motivicRawBaseEvaluationComparison k 2 2).symm
          (WeightTwoSymbols.graphSymbol k a b)) := by
  rw [finiteTensorSymbol_eq_reduction]
  congr 1

/-- The finite cone comparison carries the symbol through the canonical integral cone map. -/
theorem finiteTensorSymbol_cone_comparison (n : ℕ)
    (x : Additive kˣ ⊗[ℤ] Additive kˣ) :
    motivicFiniteBaseConeComparison k 2 2 n (finiteTensorSymbol k n x) =
      _root_.CochainComplex.finiteCoefficients.integralHomology (motivicBaseComplex k 2) n 2
        (motivicBaseEvaluationComparison k 2 2 (WeightTwoSymbols.motivicTensorSymbol k x)) :=
  motivicBaseIntegralReduction_comparison k 2 2 n _

/-- The top-degree comparison sends the finite symbol to its integral coset. -/
theorem finiteTensorSymbol_topDegree_comparison (n : ℕ)
    (x : Additive kˣ ⊗[ℤ] Additive kˣ) :
    FieldTopDegree.topDegreeFiniteEquiv k 2 n (finiteTensorSymbol k n x) =
      (QuotientAddGroup.mk (WeightTwoSymbols.motivicTensorSymbol k x) :
        FieldTopDegree.integralModulo k 2 n) :=
  FieldTopDegree.topDegreeFiniteEquiv_integralReduction k 2 n _

/-- Every genuine finite weight-two symbol is annihilated by its coefficient level. -/
theorem nsmul_finiteTensorSymbol (n : ℕ) (x : Additive kˣ ⊗[ℤ] Additive kˣ) :
    n • finiteTensorSymbol k n x = 0 :=
  FieldTopDegree.nsmul_eq_zero k 2 n _

/-- The original finite tensor symbol vanishes at coefficient level one. -/
@[simp] theorem finiteTensorSymbol_one (x : Additive kˣ ⊗[ℤ] Additive kˣ) :
    finiteTensorSymbol k 1 x = 0 := by
  simpa only [one_nsmul] using nsmul_finiteTensorSymbol k 1 x

end Motivic.WeightTwoFiniteSymbols
