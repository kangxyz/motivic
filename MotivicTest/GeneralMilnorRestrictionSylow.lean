/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.KTheory.MilnorK.RestrictionSylow
import Lean.Util.CollectAxioms

/-! Original-group Sylow detection without a canonical norm assumption. -/

namespace MotivicTest.GeneralMilnorRestrictionSylow

open Motivic.KTheory.MilnorK

variable (k Ω : Type*) [Field k] [Field Ω] [Algebra k Ω]
  [FiniteDimensional k Ω] [IsGalois k Ω]

/-- Every prime has its own actual Sylow fixed-field restriction. -/
theorem original_joint_detection (n : ℕ) (x y : K k n)
    (hxy : ∀ (p : ℕ) (_hp : p.Prime),
      ∃ S : Sylow p (Ω ≃ₐ[k] Ω),
        map n (algebraMap k
          (IntermediateField.fixedField (S : Subgroup (Ω ≃ₐ[k] Ω)))) x =
        map n (algebraMap k
          (IntermediateField.fixedField (S : Subgroup (Ω ≃ₐ[k] Ω)))) y) : x = y :=
  eq_of_sylow_restrictions k Ω n x y hxy

end MotivicTest.GeneralMilnorRestrictionSylow

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`Motivic.KTheory.MilnorK,
    `MotivicTest.GeneralMilnorRestrictionSylow]
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
  logInfo m!"Checked {names.size} Sylow restriction and Milnor declarations: \
    standard axioms only."
