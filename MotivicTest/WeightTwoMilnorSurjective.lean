/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightTwo.MilnorSurjective
public import Lean.Util.CollectAxioms

/-! # Consumers in the original raw, derived, and finite weight-two groups -/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory AlgebraicGeometry Motivic
open MilnorK.K2 WeightTwoMilnorSymbol WeightTwoMilnorSurjective

universe u

namespace MotivicTest.WeightTwoMilnorSurjective

variable (k : Type u) [Field k] [CharZero k]

/-- The target is the original raw homology, not an abstract replacement group. -/
theorem actual_raw_preimage (x : (motivicRawBaseComplex k 2).homology 2) :
    ∃ y : MilnorK.K2.Group k, rawMilnorSymbol k y = x := rawMilnorSymbol_surjective k x

/-- A signed actual cycle keeps every original coefficient in its Milnor preimage. -/
theorem actual_signed_cycle (α : WeightOnePointNorm.point k ⟶ WeightTwoSymbols.target k)
    (n : ℤ) :
    rawMilnorSymbol k (cyclePreimage k (n • α)) =
      n • WeightTwoSymbols.cycleClass k α := by
  rw [rawMilnorSymbol_cyclePreimage, map_zsmul]

/-- Use the standard derived category of Nisnevich sheaves over the base field in this test. -/
local instance instHasDerivedCategoryMotivicTest : HasDerivedCategory
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}) :=
  HasDerivedCategory.standard _

/-- The original derived integral group is reached by its original symbol map. -/
theorem actual_derived_preimage
    (x : motivicCohomology k 2 2 (SmoothSite.base (Spec (.of k)))) :
    ∃ y : MilnorK.K2.Group k, motivicMilnorSymbol k y = x := motivicMilnorSymbol_surjective k x

/-- Arbitrary coefficient levels, including zero, one, and composite levels. -/
theorem actual_finite_preimage (n : ℕ)
    (x : motivicFiniteCohomology k 2 2 n (SmoothSite.base (Spec (.of k)))) :
    ∃ y : MilnorK.K2.Group k, finiteMilnorSymbol k n y = x := finiteMilnorSymbol_surjective k n x

/-- The literal quotient by n-multiples maps onto the original finite group. -/
theorem actual_modulo_preimage (n : ℕ)
    (x : motivicFiniteCohomology k 2 2 n (SmoothSite.base (Spec (.of k)))) :
    ∃ y : milnorModulo k n, finiteMilnorSymbolModulo k n y = x :=
  finiteMilnorSymbolModulo_surjective k n x

open Lean in
run_cmd do
  for name in #[``rawMilnorSymbol_cyclePreimage, ``rawMilnorSymbol_surjective,
      ``motivicMilnorSymbol_surjective, ``finiteMilnorSymbol_surjective,
      ``finiteMilnorSymbolModulo_surjective, ``actual_raw_preimage,
      ``actual_signed_cycle, ``actual_derived_preimage,
      ``actual_finite_preimage, ``actual_modulo_preimage] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual weight-two Milnor symbol surjectivity uses only standard foundations."

end MotivicTest.WeightTwoMilnorSurjective
