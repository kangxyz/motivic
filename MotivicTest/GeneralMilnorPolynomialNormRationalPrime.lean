/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.KTheory.MilnorK.PolynomialNormRationalPrime
import Lean.Util.CollectAxioms

/-! Direct original-group prime-normal rational residue consumer. -/

namespace MotivicTest.GeneralMilnorPolynomialNormRationalPrime

open Motivic.KTheory.MilnorK Polynomial Polynomial.LocalResidue
open Motivic.KTheory.MilnorK.PolynomialResidue
open Motivic.KTheory.MilnorK.PolynomialNorm

variable {k : Type*} [Field k] [CharZero k]

local instance : Fact (Irreducible (X : k[X])) := ⟨irreducible_X⟩
local instance (p : MonicIrreducible k) :
    Fact (Irreducible (X : (AdjoinRoot p.val)[X])) := ⟨irreducible_X⟩

/-- Equality of actual original maps, without a completion or residue premise. -/
theorem original_prime_residue_square
    (p : MonicIrreducible k) [Normal k (AdjoinRoot p.val)]
    (hp : p.val.natDegree.Prime) (n : ℕ) :
    ((map n (InfinityResidue.rootXEquiv k).toRingHom).comp
      (residueAt (X : k[X]) n)).comp (rationalFunctionNorm (n + 1) p) =
      (polynomialNorm n p).comp
        ((map n (InfinityResidue.rootXEquiv (AdjoinRoot p.val)).toRingHom).comp
          (residueAt (X : (AdjoinRoot p.val)[X]) n)) := by
  apply LinearMap.ext
  exact residueAt_X_rationalFunctionNorm_prime p hp n

end MotivicTest.GeneralMilnorPolynomialNormRationalPrime

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`Motivic.KTheory.MilnorK,
    `MotivicTest.GeneralMilnorPolynomialNormRationalPrime]
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
  logInfo m!"Checked {names.size} prime rational norm and Milnor declarations: \
    standard axioms only."
