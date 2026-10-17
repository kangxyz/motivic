/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.KTheory.MilnorK.ConstantRestriction
import Motivic.KTheory.MilnorK.LowDegree
import Lean.Util.CollectAxioms

/-! Consumers of the actual rational constant-field split injection, including
arbitrary quotient classes and the integer and unit identifications in low degrees. -/

open Motivic.KTheory MilnorK Polynomial
open MilnorK.PolynomialResidue MilnorK.InfinityResidue MilnorK.ConstantRestriction

namespace MotivicTest.GeneralMilnorConstantRestriction

variable (k : Type*) [Field k]

local instance : Fact (Irreducible (X : k[X])) := ⟨irreducible_X⟩

/-- The left inverse consists of the actual DVR specialization and residue-field map. -/
theorem explicit_composition (n : ℕ) :
    ((MilnorK.map n (rootXEquiv k).toRingHom).comp
      (specializeAt (X : k[X]) n)).comp
        (MilnorK.map n (RatFunc.C : k →+* RatFunc k)) = LinearMap.id :=
  specializeZero_comp_constants k n

/-- Recovery holds for arbitrary quotient classes, rather than only pure symbols. -/
theorem all_class_left_inverse (n : ℕ) (x : K k n) :
    specializeZero k n (MilnorK.map n (RatFunc.C : k →+* RatFunc k) x) = x :=
  specializeZero_constants k n x

/-- The actual embedding detects equality of arbitrary classes in every degree. -/
theorem all_class_injective (n : ℕ) (x y : K k n)
    (h : MilnorK.map n (RatFunc.C : k →+* RatFunc k) x =
      MilnorK.map n (RatFunc.C : k →+* RatFunc k) y) : x = y :=
  constants_injective k n h

/-- Restriction really embeds each constant coordinate in the rational-function field. -/
theorem literal_constant_symbol (n : ℕ) (a : SymbolTuple k n) :
    MilnorK.map n (RatFunc.C : k →+* RatFunc k) (symbol a) =
      symbol (Units.map RatFunc.C.toMonoidHom ∘ a) :=
  constants_symbol k n a

/-- Every integer is recovered in degree zero, including non-symbol multiples. -/
theorem degree_zero_integer (z : ℤ) :
    zeroEquiv k (specializeZero k 0
      (MilnorK.map 0 (RatFunc.C : k →+* RatFunc k) ((zeroEquiv k).symm z))) = z := by
  rw [specializeZero_constants, LinearEquiv.apply_symm_apply]

/-- Degree-one recovery is literal equality of the original field unit. -/
theorem degree_one_unit (a : kˣ) :
    (oneEquiv k (specializeZero k 1
      (symbol (fun _ : Fin 1 => constantUnit k a)))).toMul = a := by
  change (oneEquiv k (specializeZero k 1
    (symbol (constantUnit k ∘ (fun _ : Fin 1 => a))))).toMul = a
  rw [specializeZero_constant_symbols, oneEquiv_symbol]
  rfl

/-- Recovery in degree one also holds for arbitrary classes through the unit equivalence. -/
theorem degree_one_all_classes (x : K k 1) :
    oneEquiv k (specializeZero k 1
      (MilnorK.map 1 (RatFunc.C : k →+* RatFunc k) x)) = oneEquiv k x := by
  rw [specializeZero_constants]

end MotivicTest.GeneralMilnorConstantRestriction

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`Motivic.KTheory.MilnorK, `MotivicTest.GeneralMilnorConstantRestriction]
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
  logInfo m!"Checked {names.size} constant-field restriction and general Milnor declarations: \
    standard axioms only."
