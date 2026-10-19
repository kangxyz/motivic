/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Diagonal.MilnorMixedNorm
public import Lean.Util.CollectAxioms

/-! Audit of actual all-weight mixed norm compatibility. -/

open Lean in
run_cmd do
  for name in #[
      ``MilnorK.oneEquiv_finiteExtensionNorm,
      ``MilnorK.finiteExtensionNorm_productUnit_constants,
      ``Motivic.DiagonalMixedPointNorm.finite_point_varying,
      ``Motivic.DiagonalCorestrictionMixed.pointPushforward_varying,
      ``Motivic.DiagonalCorestrictionMixed.corestriction_graphSymbol_varying,
      ``Motivic.DiagonalMilnorMixedNorm.raw_mixed] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original all-weight mixed norm comparison: standard foundations only."
