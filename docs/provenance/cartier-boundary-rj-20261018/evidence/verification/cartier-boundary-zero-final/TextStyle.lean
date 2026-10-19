import Mathlib.Tactic.Linter.TextBased

/-! Exact-file text/style validation of actual Cartier boundary zero and positive direct image. -/

open Lean Mathlib.Linter.TextBased in
run_cmd do
  let options : Lean.Linter.LinterOptions := {
    toOptions := ← getOptions
    linterSets := (Lean.Linter.linterSetsExt.getState (← getEnv)).merged }
  let modules := #[`Motivic.AlgebraicGeometry.SmoothSiteCartierCylinderComparison,
    `Motivic.AlgebraicGeometry.SmoothSiteCartierPunctureComparison,
    `Motivic.Cohomology.A1.PresheafBoundaryCoefficientIso,
    `Motivic.Cohomology.A1.PresheafSmoothCartierBoundaryZero,
    `Motivic.Cohomology.SheafCohomologyCartierBoundaryZero,
    `Motivic.Cohomology.A1.PresheafBoundaryOpenZero,
    `Motivic.AlgebraicGeometry.Sites.FiniteEtalePointInverseImageComposition,
    `Motivic.Cohomology.A1.PresheafBoundaryPointComparison,
    `Motivic.Cohomology.A1.PresheafBoundaryOpenSupport,
    `Motivic.Cohomology.A1.PresheafBoundaryEtaleLocalization,
    `Motivic.Cohomology.A1.PresheafBoundaryEtaleExcision,
    `MotivicTest.SheafCohomologyCartierBoundaryZero]
  let errors ← lintModules options #[] modules .humanReadable false
  let casingErrors ← modulesNotUpperCamelCase options modules
  let filenameErrors ← modulesOSForbidden options modules
  unless errors == 0 && casingErrors == 0 && filenameErrors == 0 do
    throwError "Actual Cartier boundary/direct-image text/style checks failed."
  logInfo "Pinned Lean text/style checks passed for all twelve selected modules."
