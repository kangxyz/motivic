/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.StrictInvariance
import all Motivic.Cohomology.A1.ContractionChartHigherImageVanishing
import all Motivic.Cohomology.A1.PointedCylinderPositiveRestriction
import all Motivic.Cohomology.A1.PointedCartierPositiveRestriction
import all Motivic.Cohomology.A1.StrictInvariance
import Mathlib.Tactic.Linter.TextBased
import Lean.Util.CollectAxioms
import Batteries.Tactic.Lint

/-! # The actual all-degree affine-line projection over infinite perfect fields

These consumers retain every original ordinary cohomology group and the literal
projection map. They assume only HI transfer coefficients, not any puncture-Mono
family, supported-cohomology vanishing, or positive-degree invariance. The audit
covers the three actual higher-degree producers, the final induction join, and
this consumer. Finite-field descent is outside this endpoint.
-/

public noncomputable section
open CategoryTheory AlgebraicGeometry Motivic
universe u
namespace MotivicTest.StrictA1Invariance

variable (k : Type u) [Field k] [Infinite k] [PerfectField k]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The literal ordinary projection in every degree is an isomorphism, without a supplied
puncture monomorphism or positive-degree invariance premise. -/
theorem original_allDegree_projection_isIso (F : SheafWithTransfers.{u + 1} k)
    (hF : F.obj.IsA1Invariant) (n : ℕ) (X : SmoothSite (Spec (.of k))) :
    IsIso (A1.projectionPullback (.of k)
      (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k)))
          ((SheafWithTransfers.toSheaf k).obj F) n) X) :=
  SheafWithTransfers.isStrictA1Invariant_of_isA1Invariant F hF n X

/-- The same actual all-degree projection is bijective on its original underlying group. -/
theorem original_allDegree_projection_bijective (F : SheafWithTransfers.{u + 1} k)
    (hF : F.obj.IsA1Invariant) (n : ℕ) (X : SmoothSite (Spec (.of k))) :
    Function.Bijective (A1.projectionPullback (.of k)
      (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k)))
          ((SheafWithTransfers.toSheaf k).obj F) n) X) :=
  (ConcreteCategory.isIso_iff_bijective _).mp (original_allDegree_projection_isIso k F hF n X)

open Lean Batteries.Tactic.Lint in
run_cmd do
  let env ← getEnv
  let sourceModules := #[`Motivic.Cohomology.A1.ContractionChartHigherImageVanishing,
    `Motivic.Cohomology.A1.PointedCylinderPositiveRestriction,
    `Motivic.Cohomology.A1.PointedCartierPositiveRestriction,
    `Motivic.Cohomology.A1.StrictInvariance]
  let modules := env.header.moduleNames.map (sourceModules.contains ·)
  let declarations := env.constants.map₁.fold
    (init := ← Lean.Elab.Command.liftCoreM getDeclsInCurrModule) fun declarations name _ =>
      if modules[env.const2ModIdx[name]?.get!]! then declarations.push name else declarations
  unless declarations.size ≥ 10 do
    throwError "The actual higher producers and strict-invariance declarations are missing."
  for name in declarations do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  let linters ← Lean.Elab.Command.liftCoreM (getChecks true none none)
  unless !linters.isEmpty do
    throwError "No declaration linters were selected."
  let results ← Lean.Elab.Command.liftCoreM <|
    Lean.withExporting (isExporting := false) (lintCore declarations linters)
  let mut failed := false
  for (linter, findings) in results do
    for (name, message) in findings.toArray do
      logError m!"{linter.name}: {name}: {message}"
      failed := true
  if failed then
    throwError "The exact-origin declaration lint found errors."
  logInfo m!"Original all-degree strict invariance: {declarations.size} declarations passed."

open Lean Mathlib.Linter.TextBased in
run_cmd do
  let options : Lean.Linter.LinterOptions := {
    toOptions := ← getOptions
    linterSets := (Lean.Linter.linterSetsExt.getState (← getEnv)).merged }
  let modules := #[`Motivic.Cohomology.A1.ContractionChartHigherImageVanishing,
    `Motivic.Cohomology.A1.PointedCylinderPositiveRestriction,
    `Motivic.Cohomology.A1.PointedCartierPositiveRestriction,
    `Motivic.Cohomology.A1.StrictInvariance, `MotivicTest.StrictA1Invariance]
  let errors ← lintModules options #[] modules .humanReadable false
  let casingErrors ← modulesNotUpperCamelCase options modules
  let filenameErrors ← modulesOSForbidden options modules
  unless errors == 0 && casingErrors == 0 && filenameErrors == 0 do
    throwError "Strict-invariance text/style checks failed."
  logInfo "Pinned Lean text/style passed for five exact strict-invariance sources."

end MotivicTest.StrictA1Invariance
