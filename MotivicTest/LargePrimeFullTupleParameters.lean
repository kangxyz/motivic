/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Bertini.ProjectiveScalarEvaluationAvoidance
public import Motivic.Aglib.RingTheory.Bertini.MovingPointScalarBadPointExclusion
public import Motivic.Aglib.RingTheory.Bertini.SelectedDeterminantScalarEvaluation
public import Motivic.Aglib.RingTheory.Bertini.SimultaneousFullTuplePolynomial
public import Motivic.Aglib.RingTheory.Bertini.LargePrimeFullTupleParameters
import all Motivic.Aglib.RingTheory.Bertini.ProjectiveScalarEvaluationAvoidance
import all Motivic.Aglib.RingTheory.Bertini.MovingPointScalarBadPointExclusion
import all Motivic.Aglib.RingTheory.Bertini.SelectedDeterminantScalarEvaluation
import all Motivic.Aglib.RingTheory.Bertini.SimultaneousFullTuplePolynomial
import all Motivic.Aglib.RingTheory.Bertini.LargePrimeFullTupleParameters
public import Lean.Util.CollectAxioms
public import Batteries.Tactic.Lint
public import Mathlib.Tactic.Linter.TextBased

/-! # Original chart relations and the actual two-prime full-tuple consumer -/

@[expose] public noncomputable section

open MvPolynomial

namespace MotivicTest.LargePrimeFullTupleParameters

universe u

/-- The actual original projective incidence quotient has no field-valued point
with these scalar parameters. No rationality or infinite-field premise occurs. -/
theorem original_projective_equations_excluded
    (k A K : Type u) [Field k] [CommRing A] [Field K]
    [Algebra k A] [Algebra k K] [Algebra A K] [IsScalarTower k A K]
    {N : Type u} [Fintype N] (a : N → A) (n : ℕ)
    (f : MvPolynomial (Fin n × N) k)
    (hf : ProjectiveEvaluationIncidence.parameterMap A k a n f = 0)
    (c : Fin n × N → K) (hc : eval₂ (algebraMap k K) c f ≠ 0) :
    ¬ ∀ i, ∑ e, c (i, e) * algebraMap A K (a e) = 0 :=
  ProjectiveEvaluationIncidence.not_vanish_of_eval₂_relation k A K a n f hf c hc

open Lean Batteries.Tactic.Lint in
run_cmd do
  let env ← getEnv
  let sourceModules := #[
    `Motivic.Aglib.RingTheory.Bertini.ProjectiveScalarEvaluationAvoidance,
    `Motivic.Aglib.RingTheory.Bertini.MovingPointScalarBadPointExclusion,
    `Motivic.Aglib.RingTheory.Bertini.SelectedDeterminantScalarEvaluation,
    `Motivic.Aglib.RingTheory.Bertini.SimultaneousFullTuplePolynomial,
    `Motivic.Aglib.RingTheory.Bertini.LargePrimeFullTupleParameters]
  let modules := env.header.moduleNames.map (sourceModules.contains ·)
  let declarations := env.constants.map₁.fold
    (init := ← Lean.Elab.Command.liftCoreM getDeclsInCurrModule) fun declarations name _ =>
      if modules[env.const2ModIdx[name]?.get!]! then declarations.push name else declarations
  unless declarations.size ≥ 10 do
    throwError "Exact-origin full-tuple scalar parameter declarations are missing."
  for name in declarations do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  let linters ← Lean.Elab.Command.liftCoreM (getChecks true none none)
  unless !linters.isEmpty do
    throwError "No declaration linters selected."
  let results ← Lean.Elab.Command.liftCoreM <|
    Lean.withExporting (isExporting := false) (lintCore declarations linters)
  for (linter, findings) in results do
    for (name, message) in findings.toArray do
      throwError "{linter.name}: {name}: {message}"
  logInfo m!"All {declarations.size} exact-origin declarations: lint and standard axioms passed."

open Lean Mathlib.Linter.TextBased in
run_cmd do
  let options : Lean.Linter.LinterOptions := {
    toOptions := ← getOptions
    linterSets := (Lean.Linter.linterSetsExt.getState (← getEnv)).merged }
  let modules := #[
    `Motivic.Aglib.RingTheory.Bertini.ProjectiveScalarEvaluationAvoidance,
    `Motivic.Aglib.RingTheory.Bertini.MovingPointScalarBadPointExclusion,
    `Motivic.Aglib.RingTheory.Bertini.SelectedDeterminantScalarEvaluation,
    `Motivic.Aglib.RingTheory.Bertini.SimultaneousFullTuplePolynomial,
    `Motivic.Aglib.RingTheory.Bertini.LargePrimeFullTupleParameters,
    `MotivicTest.LargePrimeFullTupleParameters]
  let errors ← lintModules options #[] modules .humanReadable false
  let casingErrors ← modulesNotUpperCamelCase options modules
  let filenameErrors ← modulesOSForbidden options modules
  unless errors == 0 && casingErrors == 0 && filenameErrors == 0 do
    throwError "Exact-file source text/style checks failed."
  logInfo "Pinned text/style checks passed for all six selected modules."

end MotivicTest.LargePrimeFullTupleParameters
