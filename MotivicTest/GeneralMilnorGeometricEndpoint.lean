/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.Cohomology.Motivic.AffineEndpointGeometricNorm
import Motivic.Cohomology.Motivic.DiagonalBoundaryFiberEvaluation
import Motivic.Cohomology.Motivic.DiagonalBoundaryEvaluation
import Lean.Util.CollectAxioms

/-! Original full geometric endpoint norm sums and actual singular cofaces. -/

open Lean in
run_cmd do
  let env ← getEnv
  let names := #[
    `Motivic.AffineEndpointGeometricNorm.geometricEndpointValue_eq,
    `Motivic.AffineEndpointGeometricNorm.geometricEndpointValue_eq_endpoint,
    `Motivic.DiagonalBoundarySupport.affineFiberIso_inv_fst,
    `Motivic.DiagonalBoundarySupport.affineFiberIso_inv_snd,
    `Motivic.DiagonalBoundarySupport.cycleValue_endpoint_generator,
    `Motivic.DiagonalBoundaryEvaluation.degreeZeroNorm_face_quotient]
  for name in names do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration {name} is missing from the checked environment"
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual full geometric endpoint sums and singular cofaces: standard axioms only."
