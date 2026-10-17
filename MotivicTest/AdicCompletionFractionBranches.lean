/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.Aglib.RingTheory.AdicCompletion.FractionTensorBranches
import Motivic.Aglib.RingTheory.AdicCompletion.FiniteRank
import Motivic.Aglib.RingTheory.AdicCompletion.BranchFractionFinite
import Lean.Util.CollectAxioms

/-! The actual original branch field product and all required scalar structures. -/

open Lean in
run_cmd do
  let env ← getEnv
  let names := #[`AdicCompletion.powAlgEquiv,
    `AdicCompletion.mapIdealLinearEquiv,
    `AdicCompletion.tensorEquivExtendedCompletionBase,
    `AdicCompletion.finrank_extendedCompletion,
    `AdicCompletion.localCompletionBaseIsScalarTower,
    `AdicCompletion.localCompletionBaseFinite,
    `AdicCompletion.localCompletionBase_injective,
    `AdicCompletion.localCompletionBase_isLocalHom,
    `AdicCompletion.localCompletionFractionIsScalarTower,
    `AdicCompletion.localCompletionFractionFinite,
    `IsDiscreteValuationRing.isLocalizationAway_of_finite,
    `IsDiscreteValuationRing.fractionPiAwayAlgEquiv,
    `AdicCompletion.fractionCompletionBaseChangeAlgEquiv,
    `AdicCompletion.fractionTensorEquivLocalFractionFields,
    `AdicCompletion.fractionTensorEquivLocalFractionFields_one_tmul]
  for name in names do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration {name} is missing from the checked environment"
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual original completed branch fraction tensor product: standard axioms only."
