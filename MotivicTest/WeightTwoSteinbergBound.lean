/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.WeightTwoSteinbergBound
public import Lean.Util.CollectAxioms

/-!
# Consumers of the proved universal bound and actual Steinberg relation

The bound is proved rather than supplied. The final equality lies in the
original raw H22 and needs neither a presentation nor a comparison axiom.
-/

@[expose] public noncomputable section

open Motivic WeightTwoSymbols WeightTwoSteinbergBound WeightTwoSteinbergTorsion

universe u

namespace MotivicTest.WeightTwoSteinbergBound

/-- The uniform bound is an unconditional theorem of the original graph construction. -/
theorem actual_universal_bound : UniversalSteinbergAnnihilator.{u} 12 :=
  universalSteinbergAnnihilator_twelve

/-- The positive bound even works before imposing characteristic zero. -/
theorem actual_bound_any_characteristic (F : Type u) [Field F] (a b : Fˣ)
    (hab : (b : F) = 1 - (a : F)) :
    (12 : ℕ) • (graphSymbol F a b : (motivicRawBaseComplex F 2).homology 2) = 0 :=
  twelve_nsmul_graphSymbol a b hab

/-- No assumed annihilator or Steinberg comparison remains in the final consumer. -/
theorem actual_raw_steinberg (F : Type u) [Field F] [CharZero F] (a b : Fˣ)
    (hab : (b : F) = 1 - (a : F)) :
    (graphSymbol F a b : (motivicRawBaseComplex F 2).homology 2) = 0 :=
  graphSymbol_steinberg a b hab

/-- The usual field-element form uses its genuine complementary pair of units. -/
theorem actual_element_steinberg (F : Type u) [Field F] [CharZero F]
    (a : F) (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    graphSymbol F (Units.mk0 a ha0)
      (Units.mk0 (1 - a) (sub_ne_zero.mpr ha1.symm)) = 0 :=
  graphSymbol_steinberg _ _ rfl

/-- A concrete arithmetic field consumes the final theorem directly. -/
theorem rational_steinberg : graphSymbol ℚ (Units.mk0 2 (by norm_num))
    (Units.mk0 (-1) (by norm_num)) = 0 := by
  apply graphSymbol_steinberg
  norm_num

open Lean in
run_cmd do
  for name in #[``cube_eq_one_of_quadratic, ``complement_product,
      ``cubicZero_factorization, ``cubicOne_factorization, ``cubic_symbol_relation,
      ``two_nsmul_cube_symbol, ``polynomial_annihilator_descent,
      ``six_nsmul_symbol_of_quadratic_root, ``twelve_nsmul_graphSymbol,
      ``universalSteinbergAnnihilator_twelve, ``graphSymbol_steinberg,
      ``actual_universal_bound, ``actual_bound_any_characteristic,
      ``actual_raw_steinberg, ``actual_element_steinberg, ``rational_steinberg] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "The actual uniform bound and Steinberg relation use only standard foundations."

end MotivicTest.WeightTwoSteinbergBound
