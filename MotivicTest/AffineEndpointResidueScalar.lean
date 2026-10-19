/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightTwo.Endpoints.ResidueScalar
public import Lean.Util.CollectAxioms

/-! Original branch fields and actual fiber fields have identical scalar norm actions. -/

open Motivic.AffineEndpointResidueScalar
open Lean in
run_cmd do
  for name in #[``fiberBase_eq, ``schemeScalar_eq,
      ``originalBranchResidueEquiv_evaluation, ``originalBranchResidueEquiv_base,
      ``norm_originalBranch, ``residueValue_original_units] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original scalar actions and actual fiber residue norms: standard foundations only."
