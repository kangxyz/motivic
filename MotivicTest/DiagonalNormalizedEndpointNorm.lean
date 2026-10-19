/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.Cohomology.Diagonal.NormalizedEndpointNorm
import Lean.Util.CollectAxioms

/-! Unconditional original endpoint cycle equality in all Milnor degrees. -/

open Lean in
run_cmd do
  let env ← getEnv
  let names := #[
    `Motivic.DiagonalBoundarySupport.normalizedAffineFiber_coordinate,
    `Motivic.DiagonalBoundarySupport.cycleValue_endpoint_normalized,
    `Motivic.DiagonalBoundarySupport.normalizedEndpointValue_eq_all,
    `Motivic.DiagonalBoundarySupport.cycleValue_endpoint_generator_eq]
  for name in names do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration {name} is missing from the checked environment"
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual all-weight endpoint cycle equality: standard axioms only."
