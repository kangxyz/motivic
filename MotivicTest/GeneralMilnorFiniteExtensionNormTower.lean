/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.KTheory.MilnorK.FiniteExtensionNormTower
import Lean.Util.CollectAxioms

/-! General actual finite-field tower compatibility, with no independence premise. -/

namespace MotivicTest.GeneralMilnorFiniteExtensionNormTower

open Motivic.KTheory.MilnorK

universe u

/-- The original fields and coefficient tower give the actual map equality,
without normality, prime-degree, or supplied norm compatibility assumptions. -/
theorem original_general_norm_tower
    {k L E : Type u} [Field k] [CharZero k] [Field L] [CharZero L] [Field E]
    [Algebra k L] [Algebra L E] [Algebra k E] [IsScalarTower k L E]
    [FiniteDimensional k L] [FiniteDimensional L E] [FiniteDimensional k E]
    (n : ℕ) :
    finiteExtensionNorm k E n = (finiteExtensionNorm k L n).comp (finiteExtensionNorm L E n) := by
  apply LinearMap.ext
  exact finiteExtensionNorm_tower L E n

end MotivicTest.GeneralMilnorFiniteExtensionNormTower

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`AdjoinRoot, `Motivic.KTheory.MilnorK,
    `MotivicTest.GeneralMilnorFiniteExtensionNormTower]
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
  logInfo m!"Checked {names.size} general finite norm tower and Milnor declarations: \
    standard axioms only."
