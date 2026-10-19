/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.MilnorK.AffineEndpointGeometry
import Lean.Util.CollectAxioms

/-! Original endpoint multiplicities and original ground-field norms. -/

open Lean in
run_cmd do
  let env ← getEnv
  let names := #[
    `MilnorK.AffineEndpointGeometry.fundamentalCoefficient_eq_originalOrder,
    `MilnorK.AffineEndpointGeometry.originalBranchResidueEquiv_scalar,
    `MilnorK.DedekindStalkResidue.value_scalar_eq_stalkLength,
    `MilnorK.DedekindResidue.endpointWeightedResidueSum_eq_baseNormSum]
  for name in names do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration {name} is missing from the checked environment"
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original endpoint coefficients and residue maps: standard axioms only."
