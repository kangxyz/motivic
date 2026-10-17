/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.KTheory.MilnorK.FiniteExtensionNormRationalZeroResiduePrime
import Lean.Util.CollectAxioms

/-! Direct original-field consumers of the normal-prime and degree-one
normalized zero-place norm squares. No norm-residue premise is supplied. -/

open Polynomial Polynomial.LocalResidue
open Motivic.KTheory MilnorK
open scoped RatFunc

attribute [local instance] Polynomial.algebra MilnorK.zeroRationalFinite

namespace MotivicTest.GeneralMilnorFiniteExtensionNormRationalZeroResiduePrime

universe u

/-- The actual prime-normal square has arbitrary original fields and classes. -/
theorem original_prime_normal_square
    {k : Type u} [Field k] [CharZero k] (L : Type u) [Field L]
    [Algebra k L] [FiniteDimensional k L] [Normal k L]
    (hp : (Module.finrank k L).Prime) (n : ℕ) (x : K (RatFunc L) (n + 1)) :
    rationalZeroResidue k n (finiteExtensionNorm (RatFunc k) (RatFunc L) (n + 1) x) =
      finiteExtensionNorm k L n (rationalZeroResidue L n x) :=
  rationalZeroResidue_finiteExtensionNorm_prime L hp n x

/-- The degree-one base case does not require a normality assumption. -/
theorem original_degree_one_square
    {k : Type u} [Field k] [CharZero k] (L : Type u) [Field L]
    [Algebra k L] [FiniteDimensional k L]
    (hd : Module.finrank k L = 1) (n : ℕ) (x : K (RatFunc L) (n + 1)) :
    rationalZeroResidue k n (finiteExtensionNorm (RatFunc k) (RatFunc L) (n + 1) x) =
      finiteExtensionNorm k L n (rationalZeroResidue L n x) :=
  rationalZeroResidue_finiteExtensionNorm_degree_one L hd n x

/-- Naturality is the literal coefficient map and works in every characteristic. -/
theorem actual_coefficient_naturality
    {A B : Type*} [Field A] [Field B] (φ : A →+* B)
    (n : ℕ) (x : K (RatFunc A) (n + 1)) :
    rationalZeroResidue B n (map (n + 1) (fractionMap φ) x) =
      map n φ (rationalZeroResidue A n x) :=
  rationalZeroResidue_restrict φ n x

end MotivicTest.GeneralMilnorFiniteExtensionNormRationalZeroResiduePrime

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`Motivic.KTheory.MilnorK,
    `MotivicTest.GeneralMilnorFiniteExtensionNormRationalZeroResiduePrime]
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
  logInfo m!"Checked {names.size} actual rational zero-residue norm and Milnor declarations: \
    standard axioms only."
