/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.WeightTwoSteinbergTorsion
public import Lean.Util.CollectAxioms

/-!
# Consumers of whole-polynomial removal of universal Steinberg torsion

These consumers keep the universal bound as an explicit assumption and conclude
vanishing in the originally defined weight-two raw homology. The positive
factor need not be prime, and the field need not contain its roots.
-/

@[expose] public noncomputable section

open Motivic WeightTwoSteinbergTorsion

universe u

namespace MotivicTest.WeightTwoSteinbergTorsion

/-- An arbitrary positive factor, with no primality or root-splitting assumption. -/
theorem remove_whole_positive_factor (m p : ℕ) (hp : 0 < p)
    (h : UniversalSteinbergAnnihilator.{u} (m * p)) :
    UniversalSteinbergAnnihilator.{u} m :=
  remove_positive_factor m p hp h

/-- The conclusion lives in the original raw complex, not a symbol presentation. -/
theorem actual_raw_symbol_vanishes (n : ℕ) (hn : 0 < n)
    (h : UniversalSteinbergAnnihilator.{u} n)
    (F : Type u) [Field F] [CharZero F] (a b : Fˣ)
    (hab : (b : F) = 1 - (a : F)) :
    (WeightTwoSymbols.graphSymbol F a b : (motivicRawBaseComplex F 2).homology 2) = 0 :=
  graphSymbol_eq_zero_of_universal_annihilator n hn h F a b hab

/-- The usual `x, 1-x` form follows for every nonzero, nonidentity field element. -/
theorem field_element_symbol_vanishes (n : ℕ) (hn : 0 < n)
    (h : UniversalSteinbergAnnihilator.{u} n)
    (F : Type u) [Field F] [CharZero F] (x : F) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    WeightTwoSymbols.graphSymbol F (Units.mk0 x hx0)
      (Units.mk0 (1 - x) (sub_ne_zero.mpr hx1.symm)) = 0 :=
  graphSymbol_eq_zero_of_universal_annihilator n hn h F _ _ rfl

/-- A single composite exponent can be removed directly, without prime induction. -/
theorem composite_bound_suffices (h : UniversalSteinbergAnnihilator.{u} 6)
    (F : Type u) [Field F] [CharZero F] (a b : Fˣ)
    (hab : (b : F) = 1 - (a : F)) : WeightTwoSymbols.graphSymbol F a b = 0 :=
  graphSymbol_eq_zero_of_universal_annihilator 6 (by decide) h F a b hab

open Lean in
run_cmd do
  for name in #[``graphSymbol_pow_left, ``graphSymbol_pow_right,
      ``graphSymbol_prod_right, ``remove_positive_factor,
      ``graphSymbol_eq_zero_of_universal_annihilator,
      ``remove_whole_positive_factor, ``actual_raw_symbol_vanishes,
      ``field_element_symbol_vanishes, ``composite_bound_suffices] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Whole-polynomial Steinberg torsion removal uses only standard foundations."

end MotivicTest.WeightTwoSteinbergTorsion
