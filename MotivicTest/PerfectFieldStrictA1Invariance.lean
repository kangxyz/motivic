/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.StrictInvariancePerfectField

import all Motivic.Cohomology.A1.StrictInvariancePerfectField
import Mathlib.Tactic.Linter
import Mathlib.Tactic.Linter.TextBased

/-! # Original ordinary projections over arbitrary perfect fields

Neither consumer supplies a cardinality assumption or geometric theorem family.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry Motivic

universe u

namespace MotivicTest.PerfectFieldStrictA1Invariance

variable {k : Type u} [Field k] [PerfectField k]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The literal ordinary projection is an isomorphism in every degree. -/
theorem original_projection_isIso
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant)
    (n : ℕ) (X : SmoothSite (Spec (.of k))) :
    IsIso (A1.projectionPullback (.of k)
      (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k)))
          ((SheafWithTransfers.toSheaf k).obj F) n) X) :=
  SheafWithTransfers.isStrictA1Invariant_of_perfect F hF n X

/-- The original projection is bijective on its unchanged cohomology groups. -/
theorem original_projection_bijective
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant)
    (n : ℕ) (X : SmoothSite (Spec (.of k))) :
    Function.Bijective (A1.projectionPullback (.of k)
      (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k)))
          ((SheafWithTransfers.toSheaf k).obj F) n) X) :=
  (ConcreteCategory.isIso_iff_bijective _).mp (original_projection_isIso F hF n X)

open Lean Batteries.Tactic.Lint in
run_cmd do
  let env ← getEnv
  let sourceModules := #[`Motivic.Cohomology.A1.StrictInvariancePerfectField]
  let modules := env.header.moduleNames.map (sourceModules.contains ·)
  let declarations := env.constants.map₁.fold
    (init := ← Lean.Elab.Command.liftCoreM getDeclsInCurrModule) fun declarations name _ =>
      if modules[env.const2ModIdx[name]?.get!]! then declarations.push name else declarations
  unless declarations.size ≥ 4 do
    throwError "Exact-origin perfect-field strict invariance declarations are missing."
  for name in declarations do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  let linters ← Lean.Elab.Command.liftCoreM (getChecks true none none)
  unless !linters.isEmpty do
    throwError "No declaration linters selected."
  let results ← Lean.Elab.Command.liftCoreM <|
    Lean.withExporting (isExporting := false) (lintCore declarations linters)
  let mut failed := false
  for (linter, findings) in results do
    for (name, message) in findings.toArray do
      failed := true
      logError m!"{linter.name}: {name}: {message}"
  if failed then
    throwError "Exact-origin declaration lint failed; all findings are listed above."
  logInfo m!"All {declarations.size} exact-origin declarations: lint and standard axioms passed."

open Lean Mathlib.Linter.TextBased in
run_cmd do
  let options : Lean.Linter.LinterOptions := {
    toOptions := ← getOptions
    linterSets := (Lean.Linter.linterSetsExt.getState (← getEnv)).merged }
  let modules := #[`Motivic.Cohomology.A1.StrictInvariancePerfectField,
    `MotivicTest.PerfectFieldStrictA1Invariance]
  let errors ← lintModules options #[] modules .humanReadable false
  let casingErrors ← modulesNotUpperCamelCase options modules
  let filenameErrors ← modulesOSForbidden options modules
  unless errors == 0 && casingErrors == 0 && filenameErrors == 0 do
    throwError "Exact-file source text/style checks failed."
  logInfo "Pinned text/style checks passed for both selected modules."


end MotivicTest.PerfectFieldStrictA1Invariance
