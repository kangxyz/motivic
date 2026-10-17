/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.KTheory.MilnorK.PolynomialNormPrimeTower
import Lean.Util.CollectAxioms

/-! Actual original-field tower consumers and transitive foundation audit. -/

namespace MotivicTest.GeneralMilnorPolynomialNormPrimeTower

open Motivic.KTheory.MilnorK Polynomial Polynomial.LocalResidue
open Motivic.KTheory.MilnorK.PolynomialNorm
open Motivic.KTheory.MilnorK.PolynomialResidue

variable {k : Type*} [Field k] [CharZero k]

/-- The original top-field norm factors through the normal-prime subfield. -/
theorem original_tower_map
    (p : MonicIrreducible k) [Normal k (AdjoinRoot p.val)]
    (hp : p.val.natDegree.Prime) (h : MonicIrreducible k)
    (f : AdjoinRoot p.val →ₐ[k] AdjoinRoot h.val) (n : ℕ) :
    polynomialNorm n h = (polynomialNorm n p).comp
      ((polynomialNorm n (AdjoinRoot.towerBranch p.val h.val f).val).comp
        (map n (adjoinRootMap (algebraMap k (AdjoinRoot p.val)) h.val
          (AdjoinRoot.towerBranch p.val h.val f).val.val
          (AdjoinRoot.towerBranch p.val h.val f).property))) := by
  apply LinearMap.ext
  exact polynomialNorm_eq_prime_tower p hp h f n

end MotivicTest.GeneralMilnorPolynomialNormPrimeTower

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`Motivic.KTheory.MilnorK,
    `MotivicTest.GeneralMilnorPolynomialNormPrimeTower]
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
  logInfo m!"Checked {names.size} normal-prime tower and Milnor declarations: \
    standard axioms only."
