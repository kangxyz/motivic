/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.DiagonalMilnorCoprimeRestriction
public import Lean.Util.CollectAxioms

/-! Audit of original full-branch transfer and finite coprime restriction. -/

open Lean in
run_cmd do
  for name in #[
      ``Motivic.DiagonalMilnorNormBaseChange.corestriction_rawSymbol_baseChange_algebraMap,
      ``Motivic.DiagonalMilnorNormBaseChange.corestriction_rawSymbol_baseChange_irreducible,
      ``Motivic.DiagonalMilnorCoprimeRestriction.raw_polynomial_mixed,
      ``Motivic.DiagonalMilnorCoprimeRestriction.exists_coprime_restriction_norm_eq] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original full-branch and coprime norm comparison: standard foundations only."
