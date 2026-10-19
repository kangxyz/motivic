/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.StrictInvariance.DegreeOne
import all Motivic.Cohomology.A1.StrictInvariance.DegreeInduction
import all Motivic.Cohomology.A1.StrictInvariance.DegreeOne
import Mathlib.Tactic.Linter.TextBased
import Lean.Util.CollectAxioms
import Batteries.Tactic.Lint

/-! # The actual global H1 projection over infinite perfect fields

These consumers retain the original ordinary cohomology and projection map.
They use only HI transfer coefficients, not H1 invariance as an input. The
all-degree induction audited alongside them remains explicitly conditional
on the independent higher-degree Cartier puncture-monomorphism family.
-/

public noncomputable section
open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory AlgebraicGeometry Motivic
universe u
namespace MotivicTest.DegreeOneHomotopyInvariance

variable (k : Type u) [Field k] [Infinite k] [PerfectField k]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The literal ordinary H1 projection is an isomorphism, without a supplied
puncture monomorphism or positive-degree invariance premise. -/
theorem original_H1_projection_isIso (F : SheafWithTransfers.{u + 1} k)
    (hF : F.obj.IsA1Invariant) (X : SmoothSite (Spec (.of k))) :
    IsIso (A1.projectionPullback (.of k)
      (_root_.CategoryTheory.Sheaf.LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k)))
          ((SheafWithTransfers.toSheaf k).obj F) 1) X) :=
  SheafWithTransfers.degreeOne_isInvariant F hF X

/-- The same actual H1 projection is bijective on its original underlying group. -/
theorem original_H1_projection_bijective (F : SheafWithTransfers.{u + 1} k)
    (hF : F.obj.IsA1Invariant) (X : SmoothSite (Spec (.of k))) :
    Function.Bijective (A1.projectionPullback (.of k)
      (_root_.CategoryTheory.Sheaf.LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k)))
          ((SheafWithTransfers.toSheaf k).obj F) 1) X) :=
  (ConcreteCategory.isIso_iff_bijective _).mp (original_H1_projection_isIso k F hF X)

open Lean Batteries.Tactic.Lint in
run_cmd do
  let env ← getEnv
  let sourceModules := #[`Motivic.Cohomology.A1.StrictInvariance.DegreeInduction,
    `Motivic.Cohomology.A1.StrictInvariance.DegreeOne]
  let modules := env.header.moduleNames.map (sourceModules.contains ·)
  let declarations := env.constants.map₁.fold
    (init := ← Lean.Elab.Command.liftCoreM getDeclsInCurrModule) fun declarations name _ =>
      if modules[env.const2ModIdx[name]?.get!]! then declarations.push name else declarations
  unless declarations.size ≥ 10 do
    throwError "The actual H1 endpoint and conditional induction declarations are missing."
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
  logInfo m!"Global H1 endpoint and conditional induction: {declarations.size} declarations passed."

open Lean Mathlib.Linter.TextBased in
run_cmd do
  let options : Lean.Linter.LinterOptions := {
    toOptions := ← getOptions
    linterSets := (Lean.Linter.linterSetsExt.getState (← getEnv)).merged }
  let modules := #[`Motivic.Cohomology.A1.StrictInvariance.DegreeInduction,
    `Motivic.Cohomology.A1.StrictInvariance.DegreeOne, `MotivicTest.DegreeOneHomotopyInvariance]
  let errors ← lintModules options #[] modules .humanReadable false
  let casingErrors ← modulesNotUpperCamelCase options modules
  let filenameErrors ← modulesOSForbidden options modules
  unless errors == 0 && casingErrors == 0 && filenameErrors == 0 do
    throwError "Global H1 endpoint text/style checks failed."
  logInfo "Pinned Lean text/style passed for three exact H1 assembly sources."

end MotivicTest.DegreeOneHomotopyInvariance
