/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.KTheory.MilnorK.PolynomialNormRationalFinitePrime
import Lean.Util.CollectAxioms

/-! Direct consumers of the original full finite-place norm square. -/

namespace MotivicTest.GeneralMilnorPolynomialNormRationalFinitePrime

open Motivic.KTheory.MilnorK Polynomial Polynomial.LocalResidue
open Motivic.KTheory.MilnorK.PolynomialResidue
open Motivic.KTheory.MilnorK.PolynomialNorm

variable {k : Type*} [Field k] [CharZero k]

open scoped Classical in
/-- The finite-place square as an equality of actual integer-linear maps. -/
theorem original_finite_place_square
    (p : MonicIrreducible k) [Normal k (AdjoinRoot p.val)]
    (hp : p.val.natDegree.Prime) (h : MonicIrreducible k) (n : ℕ) :
    (residueAt h.val n).comp (rationalFunctionNorm (n + 1) p) =
      ∑ q ∈ (placesAbove (algebraMap k (AdjoinRoot p.val)) h).attach,
        (polynomialNorm n
          (AdjoinRoot.tensorSwapBranchEquiv p.val h.val
            ⟨q.val, (mem_placesAbove _ _ _).mp q.property⟩).val).comp
          ((map n (AdjoinRoot.tensorSwapBranchRingEquiv p.val h.val
            ⟨q.val, (mem_placesAbove _ _ _).mp q.property⟩).toRingHom).comp
            (residueAt q.val.val n)) := by
  apply LinearMap.ext
  intro x
  simpa only [LinearMap.comp_apply, LinearMap.sum_apply] using
    residueAt_rationalFunctionNorm_prime p hp h n x

end MotivicTest.GeneralMilnorPolynomialNormRationalFinitePrime

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`Motivic.KTheory.MilnorK,
    `MotivicTest.GeneralMilnorPolynomialNormRationalFinitePrime]
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
  logInfo m!"Checked {names.size} finite-place prime rational norm and Milnor declarations: \
    standard axioms only."
