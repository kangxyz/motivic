/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.StrictInvarianceCoefficientInputs
public import Motivic.Cohomology.A1.FiniteCoefficientLocalZero

import all Motivic.Cohomology.A1.CoefficientLocalZero
import all Motivic.Cohomology.A1.FiniteCoefficientLocalZero
import all Motivic.Cohomology.A1.ContractionBoundaryInputs
import all Motivic.Cohomology.A1.ContractionCohomologyInputs
import all Motivic.Cohomology.A1.PointedCartierH1RestrictionInputs
import all Motivic.Cohomology.A1.ContractionChartHigherImageInputs
import all Motivic.Cohomology.A1.PointedCartierPositiveRestrictionInputs
import all Motivic.Cohomology.A1.StrictInvarianceCoefficientInputs
import Mathlib.Tactic.Linter
import Mathlib.Tactic.Linter.TextBased

/-! # Original-map consumer of conditional coefficient-input strict invariance

The general tests retain both producer inputs. The finite-field consumer derives
local-zero detection from its actual producer and retains only canonical boundary
Epi as a geometric input. None asserts unconditional finite-field strict invariance.
-/

public noncomputable section
open CategoryTheory AlgebraicGeometry Motivic
universe u
namespace MotivicTest.StrictA1CoefficientInputs

section General

variable {k : Type u} [Field k]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The two original inputs suffice for the literal ordinary map in every degree. -/
theorem original_projection_isIso [PerfectField k]
    (hD : PresheafWithTransfers.IntegralAffineLocalZero k)
    (hE : FiniteEtaleSite.OriginalPresheaf.CanonicalBoundaryEpi k)
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant)
    (n : ℕ) (X : SmoothSite (Spec (.of k))) :
    IsIso (A1.projectionPullback (.of k)
      (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k)))
          ((SheafWithTransfers.toSheaf k).obj F) n) X) :=
  SheafWithTransfers.isStrictA1Invariant_of_coefficient_inputs hD hE F hF n X

/-- The empty degree-one window yields the family at all original full-K marks. -/
theorem original_H1_puncture_mono
    (hD : PresheafWithTransfers.IntegralAffineLocalZero k)
    (hE : FiniteEtaleSite.OriginalPresheaf.CanonicalBoundaryEpi k)
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant) :
    FiniteEtaleSite.SmoothCartierPunctureRestrictionMono F 1 :=
  FiniteEtaleSite.CoefficientInputs.smoothCartierPunctureRestrictionMono_one hD hE F hF

/-- Degree two uses only degree one for every HI coefficient, including F_-1. -/
theorem original_H2_puncture_mono
    (hD : PresheafWithTransfers.IntegralAffineLocalZero k)
    (hE : FiniteEtaleSite.OriginalPresheaf.CanonicalBoundaryEpi k)
    (hOne : ∀ (G : SheafWithTransfers.{u + 1} k), G.obj.IsA1Invariant →
      (SheafCohomology.withTransfers k G 1).IsA1Invariant)
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant) :
    FiniteEtaleSite.SmoothCartierPunctureRestrictionMono F 2 := by
  apply FiniteEtaleSite.CoefficientInputs.smoothCartierPunctureRestrictionMono_of_lower_degrees
    hD hE 1 ?_ F hF
  intro G hG q hq hq2
  have hq1 : q = 1 := by omega
  subst q
  exact hOne G hG

end General

section Finite

variable {k : Type u} [Field k] [Finite k]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Actual finite-field local zero removes D; only the original boundary Epi
family remains conditional in the literal ordinary projection consumer. -/
theorem finite_original_projection_isIso_of_boundary_epi
    (hE : FiniteEtaleSite.OriginalPresheaf.CanonicalBoundaryEpi k)
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant)
    (n : ℕ) (X : SmoothSite (Spec (.of k))) :
    IsIso (A1.projectionPullback (.of k)
      (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k)))
          ((SheafWithTransfers.toSheaf k).obj F) n) X) :=
  SheafWithTransfers.isStrictA1Invariant_of_coefficient_inputs
    (PresheafWithTransfers.integralAffineLocalZero_of_finite k) hE F hF n X

end Finite

open Lean Batteries.Tactic.Lint in
run_cmd do
  let env ← getEnv
  let sourceModules := #[
    `Motivic.Cohomology.A1.CoefficientLocalZero,
    `Motivic.Cohomology.A1.FiniteCoefficientLocalZero,
    `Motivic.Cohomology.A1.ContractionBoundaryInputs,
    `Motivic.Cohomology.A1.ContractionCohomologyInputs,
    `Motivic.Cohomology.A1.PointedCartierH1RestrictionInputs,
    `Motivic.Cohomology.A1.ContractionChartHigherImageInputs,
    `Motivic.Cohomology.A1.PointedCartierPositiveRestrictionInputs,
    `Motivic.Cohomology.A1.StrictInvarianceCoefficientInputs]
  let modules := env.header.moduleNames.map (sourceModules.contains ·)
  let declarations := env.constants.map₁.fold
    (init := ← Lean.Elab.Command.liftCoreM getDeclsInCurrModule) fun declarations name _ =>
      if modules[env.const2ModIdx[name]?.get!]! then declarations.push name else declarations
  unless declarations.size ≥ 30 do
    throwError "Exact-origin coefficient-input strict invariance declarations are missing."
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
    `Motivic.Cohomology.A1.CoefficientLocalZero,
    `Motivic.Cohomology.A1.FiniteCoefficientLocalZero,
    `Motivic.Cohomology.A1.ContractionBoundaryInputs,
    `Motivic.Cohomology.A1.ContractionCohomologyInputs,
    `Motivic.Cohomology.A1.PointedCartierH1RestrictionInputs,
    `Motivic.Cohomology.A1.ContractionChartHigherImageInputs,
    `Motivic.Cohomology.A1.PointedCartierPositiveRestrictionInputs,
    `Motivic.Cohomology.A1.StrictInvarianceCoefficientInputs,
    `MotivicTest.StrictA1CoefficientInputs]
  let errors ← lintModules options #[] modules .humanReadable false
  let casingErrors ← modulesNotUpperCamelCase options modules
  let filenameErrors ← modulesOSForbidden options modules
  unless errors == 0 && casingErrors == 0 && filenameErrors == 0 do
    throwError "Exact-file source text/style checks failed."
  logInfo "Pinned text/style checks passed for all nine selected modules."


end MotivicTest.StrictA1CoefficientInputs
