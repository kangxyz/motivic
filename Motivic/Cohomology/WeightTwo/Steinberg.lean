/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightTwo.SteinbergBound
public import Motivic.Cohomology.WeightTwo.FiniteSymbols

/-!
# Steinberg for the actual integral and finite-coefficient motivic symbols

The proved relation in the original raw complex transports through its actual
field-evaluation comparison and then through the original coefficient reduction.
This does not assert that the Milnor symbol map is an isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

universe w u

namespace Motivic.WeightTwoSteinberg
open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] [CharZero k]
variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The genuinely defined integral motivic symbol satisfies Steinberg. -/
theorem motivicTensorSymbol_steinberg (a b : kˣ) (hab : (a : k) + (b : k) = 1) :
    WeightTwoSymbols.motivicTensorSymbol k
      (Additive.ofMul a ⊗ₜ[ℤ] Additive.ofMul b) = 0 := by
  apply (motivicRawBaseEvaluationComparison k 2 2).injective
  rw [WeightTwoSymbols.motivicTensorSymbol_tmul_comparison, map_zero]
  exact WeightTwoSteinbergBound.graphSymbol_steinberg a b (eq_sub_iff_add_eq.mpr
    (by simpa only [add_comm] using hab))

/-- Every coefficient level uses the same proved integral relation and the
original reduction map; no invertibility condition on the level is imposed. -/
theorem finiteTensorSymbol_steinberg (n : ℕ) (a b : kˣ)
    (hab : (a : k) + (b : k) = 1) :
    WeightTwoFiniteSymbols.finiteTensorSymbol k n
      (Additive.ofMul a ⊗ₜ[ℤ] Additive.ofMul b) = 0 := by
  rw [WeightTwoFiniteSymbols.finiteTensorSymbol_eq_reduction,
    motivicTensorSymbol_steinberg k a b hab, map_zero]

end Motivic.WeightTwoSteinberg
