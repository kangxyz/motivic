/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.KTheory.MilnorK.FiniteExtensionNormRightProjection
import Lean.Util.CollectAxioms

/-! The literal rightmost base unit commutes with the original-field norm. -/

namespace MotivicTest.FiniteExtensionNormRightProjection

open Motivic.KTheory.MilnorK
open Motivic.KTheory.MilnorK2 (unitsLinear)

variable {F : Type*} [Field F]

/-- Cyclic motion retains the degree sign on actual ordered symbols. -/
theorem signed_cyclic_symbol (n : ℕ) (a : SymbolTuple F n) (b : Fˣ) :
    symbol (Fin.snoc a b) = (-1 : ℤ) ^ n • symbol (Fin.cons b a) :=
  symbol_snoc_eq_signed_cons n a b

/-- Degree-one commutation applies to arbitrary quotient classes, not just symbols. -/
theorem arbitrary_class_commutation (n : ℕ) (x : K F n) (b : Additive Fˣ) :
    productUnit n x b = (-1 : ℤ) ^ n •
      degreeCongr (Nat.one_add n) (product 1 n (unitsToOne F b) x) :=
  productUnit_eq_signed_left n x b

variable (k E : Type*) [Field k] [CharZero k] [Field E]
  [Algebra k E] [FiniteDimensional k E]

/-- No symbol decomposition or extension tower premise is required by the consumer. -/
theorem arbitrary_original_class (n : ℕ) (x : K E n) (b : Additive kˣ) :
    finiteExtensionNorm k E (n + 1)
      (productUnit n x (unitsLinear (algebraMap k E) b)) =
        productUnit n (finiteExtensionNorm k E n x) b :=
  finiteExtensionNorm_productUnit_constants_right k E n x b

/-- The empty-degree case is part of the same formula. -/
theorem degree_zero (x : K E 0) (b : Additive kˣ) :
    finiteExtensionNorm k E 1 (productUnit 0 x (unitsLinear (algebraMap k E) b)) =
      productUnit 0 (finiteExtensionNorm k E 0 x) b :=
  finiteExtensionNorm_productUnit_constants_right k E 0 x b

/-- On symbols the base unit remains in the literal final coordinate. -/
theorem literal_last_coordinate (n : ℕ) (a : SymbolTuple E n) (b : kˣ) :
    finiteExtensionNorm k E (n + 1)
      (symbol (Fin.snoc a (Units.map (algebraMap k E).toMonoidHom b))) =
        productUnit n (finiteExtensionNorm k E n (symbol a)) (Additive.ofMul b) := by
  have hu : (unitsLinear (algebraMap k E) (Additive.ofMul b)).toMul =
      Units.map (algebraMap k E).toMonoidHom b := rfl
  simpa only [productUnit_symbol, hu] using
    finiteExtensionNorm_productUnit_constants_right k E n (symbol a) (Additive.ofMul b)

end MotivicTest.FiniteExtensionNormRightProjection

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`Motivic.KTheory.MilnorK,
    `MotivicTest.FiniteExtensionNormRightProjection]
  let selected (name : Name) := prefixes.any (·.isPrefixOf name)
  let mut names : NameSet := {}
  for i in [:env.header.moduleNames.size] do
    if selected env.header.moduleNames[i]! then
      for name in env.header.moduleData[i]!.constNames do
        names := names.insert name
  names := env.constants.foldStage2 (fun names name _ =>
    if selected name then names.insert name else names) names
  for name in names.toArray do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration {name} is missing from the checked environment"
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Checked {names.size} right-unit projection and Milnor declarations: \
    standard axioms only."
