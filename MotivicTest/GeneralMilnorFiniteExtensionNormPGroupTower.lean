/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.KTheory.MilnorK.FiniteExtensionNormPGroupTower
import Lean.Util.CollectAxioms

/-! Original-field transitivity with arbitrary finite upper extension and p-group lower ambient. -/

namespace MotivicTest.GeneralMilnorFiniteExtensionNormPGroupTower

open Motivic.KTheory.MilnorK

universe u

/-- No upper-field embedding or supplied norm-tower equality is assumed. -/
theorem original_pGroup_tower
    {k L E Ω : Type u} [Field k] [CharZero k] [Field L] [CharZero L]
    [Field E] [Field Ω] [Algebra k L] [Algebra L E] [Algebra k E]
    [IsScalarTower k L E] [Algebra k Ω]
    [FiniteDimensional k L] [FiniteDimensional L E] [FiniteDimensional k E]
    [FiniteDimensional k Ω] [IsGalois k Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (hG : IsPGroup ℓ (Ω ≃ₐ[k] Ω)) (g : L →ₐ[k] Ω)
    (n : ℕ) :
    finiteExtensionNorm k E n = (finiteExtensionNorm k L n).comp (finiteExtensionNorm L E n) := by
  apply LinearMap.ext
  exact finiteExtensionNorm_tower_of_pGroup ℓ hG g n

end MotivicTest.GeneralMilnorFiniteExtensionNormPGroupTower

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`Motivic.KTheory.MilnorK,
    `MotivicTest.GeneralMilnorFiniteExtensionNormPGroupTower]
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
  logInfo m!"Checked {names.size} actual p-group lower norm towers and Milnor declarations: \
    standard axioms only."
