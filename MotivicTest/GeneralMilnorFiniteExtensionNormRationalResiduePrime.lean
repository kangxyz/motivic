/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.KTheory.MilnorK.FiniteExtensionNormRationalResiduePrime
import Lean.Util.CollectAxioms

/-! Actual rational norm, original residue norm, and every finite branch. -/

namespace MotivicTest.GeneralMilnorFiniteExtensionNormRationalResiduePrime

open Motivic.KTheory.MilnorK Polynomial PolynomialResidue PolynomialNorm AdjoinRoot
open scoped RatFunc

attribute [local instance] Polynomial.algebra AdjoinRoot.scalarBranchAlgebra
  Motivic.KTheory.MilnorK.residueRootFinite Motivic.KTheory.MilnorK.residueRootCharZero
  Motivic.KTheory.MilnorK.primeRationalFinite

universe u

/-- Direct consumption retains every original residue field and scalar map. -/
theorem original_prime_residue_square
    {k : Type u} [Field k] [CharZero k] (p : MonicIrreducible k)
    [Normal k (AdjoinRoot p.val)] (hp : p.val.natDegree.Prime)
    (h : MonicIrreducible k)
    [Fintype (IrreducibleBranch (h.val.map (algebraMap k (AdjoinRoot p.val))))]
    (n : ℕ) (x : K (RatFunc (AdjoinRoot p.val)) (n + 1)) :
    residueAt h.val n
      (finiteExtensionNorm (RatFunc k) (RatFunc (AdjoinRoot p.val)) (n + 1) x) =
      ∑ r : IrreducibleBranch (h.val.map (algebraMap k (AdjoinRoot p.val))),
        let : FiniteDimensional (AdjoinRoot h.val) (AdjoinRoot r.val.val) :=
          finiteDimensional_scalarBranch_residue h r
        finiteExtensionNorm (AdjoinRoot h.val) (AdjoinRoot r.val.val) n
          (residueAt r.val.val n x) :=
  residueAt_finiteExtensionNorm_rational_prime_root p hp h n x

/-- The rational norm previously used in residue squares is the actual field norm. -/
theorem original_rational_norm {k : Type u} [Field k] [CharZero k]
    (p : MonicIrreducible k) (n : ℕ) :
    rationalFunctionNorm n p = finiteExtensionNorm (RatFunc k) (RatFunc (AdjoinRoot p.val)) n :=
  rationalFunctionNorm_eq_finiteExtensionNorm p n

end MotivicTest.GeneralMilnorFiniteExtensionNormRationalResiduePrime

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`AdjoinRoot, `Motivic.KTheory.MilnorK,
    `MotivicTest.GeneralMilnorFiniteExtensionNormRationalResiduePrime]
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
  logInfo m!"Checked {names.size} actual rational finite residue norms and Milnor declarations: \
    standard axioms only."
