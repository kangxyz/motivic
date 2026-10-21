/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightTwo.Steinberg
public import Lean.Util.CollectAxioms

/-! # Consumers of actual derived integral and finite Steinberg symbols -/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory AlgebraicGeometry Motivic
open scoped TensorProduct

universe u

namespace MotivicTest.WeightTwoSteinberg

variable (k : Type u) [Field k] [CharZero k]

/-- The standard derived-category structure used by these Steinberg consumers. -/
local instance testHasDerivedCategory : HasDerivedCategory
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}) :=
  HasDerivedCategory.standard _

/-- The target is the original derived motivic cohomology group. -/
theorem actual_integral_symbol (a b : kˣ) (hab : (a : k) + (b : k) = 1) :
    (WeightTwoSymbols.motivicTensorSymbol k
      (Additive.ofMul a ⊗ₜ[ℤ] Additive.ofMul b) :
        motivicCohomology k 2 2 (SmoothSite.base (Spec (.of k)))) = 0 :=
  WeightTwoSteinberg.motivicTensorSymbol_steinberg k a b hab

/-- Composite levels and zero use the very same actual coefficient construction. -/
theorem actual_finite_symbol (n : ℕ) (a b : kˣ) (hab : (a : k) + (b : k) = 1) :
    (WeightTwoFiniteSymbols.finiteTensorSymbol k n
      (Additive.ofMul a ⊗ₜ[ℤ] Additive.ofMul b) :
        motivicFiniteCohomology k 2 2 n (SmoothSite.base (Spec (.of k)))) = 0 :=
  WeightTwoSteinberg.finiteTensorSymbol_steinberg k n a b hab

open Lean in
run_cmd do
  for name in #[``WeightTwoSteinberg.motivicTensorSymbol_steinberg,
      ``WeightTwoSteinberg.finiteTensorSymbol_steinberg,
      ``actual_integral_symbol, ``actual_finite_symbol] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual derived integral and finite Steinberg symbols use standard foundations."

end MotivicTest.WeightTwoSteinberg
