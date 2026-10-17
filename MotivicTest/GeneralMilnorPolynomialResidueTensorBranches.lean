/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.KTheory.MilnorK.PolynomialResidueTensorBranches
import Lean.Util.CollectAxioms

/-! Direct consumer of all original matched-branch residues. -/

namespace MotivicTest.GeneralMilnorPolynomialResidueTensorBranches

open Motivic.KTheory.MilnorK Polynomial Polynomial.LocalResidue AdjoinRoot
open Motivic.KTheory.MilnorK.PolynomialResidue

variable {k : Type*} [Field k] (p h : k[X])
  [Fact (Irreducible p)] [Fact (Irreducible h)] [CharZero (AdjoinRoot p)]

local instance (q : IrreducibleBranch (h.map (algebraMap k (AdjoinRoot p)))) :
    Fact (Irreducible (X - C (tensorBranchPlaceRoot p h q))) :=
  ⟨irreducible_X_sub_C _⟩

/-- The original residue map is retained through the whole quotient equivalence. -/
theorem original_branch_residue_square
    (q : IrreducibleBranch (h.map (algebraMap k (AdjoinRoot p)))) (n : ℕ) :
    (map n (tensorSwapBranchRingEquiv p h q).toRingHom).comp (residueAt q.val.val n) =
      (map n (linearRootEquiv (tensorBranchPlaceRoot p h q)).toRingHom).comp
        ((residueAt (X - C (tensorBranchPlaceRoot p h q)) n).comp
          (map (n + 1) (fractionMap (tensorBranchCoefficientMap p h q)))) := by
  apply LinearMap.ext
  exact residueAt_tensorBranch_linear p h q n

end MotivicTest.GeneralMilnorPolynomialResidueTensorBranches

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`Motivic.KTheory.MilnorK,
    `MotivicTest.GeneralMilnorPolynomialResidueTensorBranches]
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
  logInfo m!"Checked {names.size} tensor branch residue and Milnor declarations: \
    standard axioms only."
