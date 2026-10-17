/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.Cohomology.Motivic.DiagonalBoundarySupport
import Lean.Util.CollectAxioms

/-! Actual arbitrary-weight integral support and normalized endpoint evaluations. -/

open Lean in
run_cmd do
  let env ← getEnv
  let names := #[
    `Motivic.DiagonalBoundarySupport.scalarMap_injective,
    `Motivic.DiagonalBoundarySupport.projectionFlat,
    `Motivic.DiagonalBoundarySupport.supportIsoSpec_projection,
    `Motivic.DiagonalBoundarySupport.normalizedEndpointValue_eq]
  for name in names do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration {name} is missing from the checked environment"
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original all-weight support and normalized endpoints: standard axioms only."
