/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.KTheory.MilnorK.PolynomialNormLinearPlace
import Lean.Util.CollectAxioms

/-! Direct full-branch consumer at the original rational place. -/

namespace MotivicTest.GeneralMilnorPolynomialNormLinearPlace

open Motivic.KTheory.MilnorK Polynomial Polynomial.LocalResidue
open Motivic.KTheory.MilnorK.PolynomialResidue
open Motivic.KTheory.MilnorK.PolynomialNorm

variable {k : Type*} [Field k] [CharZero k]
variable (h : k[X]) [Fact (Irreducible h)]

local instance : Fact (Irreducible (X - C (AdjoinRoot.root h))) :=
  ⟨irreducible_X_sub_C _⟩

open scoped Classical in
/-- The entire original map agrees with the entire actual branch sum. -/
theorem original_norm_residue_map (n : ℕ) (p : MonicIrreducible (RatFunc k)) :
    (residueAt h n).comp (polynomialNorm (n + 1) p) =
      ∑ q ∈ (placesAbove (fractionMap (algebraMap k (AdjoinRoot h))) p).attach,
        (map n (linearRootEquiv (AdjoinRoot.root h)).toRingHom).comp
          ((residueAt (X - C (AdjoinRoot.root h)) n).comp
            ((polynomialNorm (n + 1) q.val).comp
              (map (n + 1)
                (adjoinRootMap (fractionMap (algebraMap k (AdjoinRoot h))) p.val q.val.val
                  ((mem_placesAbove _ p q.val).mp q.property))))) := by
  apply LinearMap.ext
  intro x
  simpa only [LinearMap.comp_apply, LinearMap.sum_apply] using
    residueAt_polynomialNorm_eq_linearPlace_sum h n p x

end MotivicTest.GeneralMilnorPolynomialNormLinearPlace

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`Motivic.KTheory.MilnorK,
    `MotivicTest.GeneralMilnorPolynomialNormLinearPlace]
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
  logInfo m!"Checked {names.size} full finite-place branch and Milnor declarations: \
    standard axioms only."
