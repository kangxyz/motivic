/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.KTheory.MilnorK.FiniteExtensionNorm
import Lean.Util.CollectAxioms

/-! Choice independence and degree law on the original finite-extension Milnor groups. -/

namespace MotivicTest.GeneralMilnorFiniteExtensionNorm

open Motivic.KTheory.MilnorK Polynomial
open Motivic.KTheory.MilnorK.PolynomialNorm
open Motivic.KTheory.MilnorK.PolynomialResidue

variable (k E : Type*) [Field k] [CharZero k] [Field E]
  [Algebra k E] [FiniteDimensional k E]

/-- Any actual presentation computes the original-field norm, without extra laws. -/
theorem any_original_presentation (n : ℕ) (p : MonicIrreducible k)
    (ε : AdjoinRoot p.val ≃ₐ[k] E) :
    finiteExtensionNorm k E n = (polynomialNorm n p).comp (map n ε.symm.toRingHom) :=
  finiteExtensionNorm_eq_presentation k E n p ε

/-- The original restriction is multiplied by the actual finite degree. -/
theorem original_degree_law (n : ℕ) (x : K k n) :
    finiteExtensionNorm k E n (map n (algebraMap k E) x) =
      (Module.finrank k E : ℤ) • x :=
  finiteExtensionNorm_map_constants k E n x

end MotivicTest.GeneralMilnorFiniteExtensionNorm

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`Motivic.KTheory.MilnorK,
    `MotivicTest.GeneralMilnorFiniteExtensionNorm]
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
  logInfo m!"Checked {names.size} actual finite-extension norms and Milnor declarations: \
    standard axioms only."
