/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.KTheory.MilnorK.FiniteExtensionNormProductBaseChange
import Lean.Util.CollectAxioms

/-! Actual field tensor coordinate maps, with no norm law assumption. -/

namespace MotivicTest.GeneralMilnorNormProductBaseChange

open Motivic.KTheory.MilnorK
open scoped TensorProduct

variable {k L ι : Type*} [Field k] [CharZero k] [Field L] [CharZero L]
  [Algebra k L] [Fintype ι]
  (D : ι → Type*) [∀ i, Field (D i)] [∀ i, Algebra L (D i)]
  [∀ i, FiniteDimensional L (D i)]

/-- Direct consumer keeps the actual tensor-coordinate restriction map. -/
theorem actual_tensor_coordinate_norms
    (E : Type*) [Field E] [Algebra k E] [FiniteDimensional k E]
    (e : L ⊗[k] E ≃ₐ[L] ∀ i, D i) (n : ℕ) (x : K E n) :
    map n (algebraMap k L) (finiteExtensionNorm k E n x) =
      ∑ i, finiteExtensionNorm L (D i) n
        (map n (((Pi.evalRingHom D i).comp e.toRingHom).comp
          Algebra.TensorProduct.includeRight.toRingHom) x) :=
  finiteExtensionNorm_restrict_tensorProduct D E e n x

end MotivicTest.GeneralMilnorNormProductBaseChange

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`AdjoinRoot, `Motivic.KTheory.MilnorK,
    `MotivicTest.GeneralMilnorNormProductBaseChange]
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
  logInfo m!"Checked {names.size} actual tensor-coordinate norm declarations: \
    standard axioms only."
