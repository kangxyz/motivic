/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.StrictInvarianceFiniteField

import all Motivic.AlgebraicGeometry.SmoothSiteAffineWeilRefinement
import all Motivic.Cohomology.A1.OriginalPresentationAffineCombinedCorrection
import all Motivic.AlgebraicGeometry.AffineCorrectionBaseRestriction
import all Motivic.Aglib.AlgebraicGeometry.RelativeCurve.OriginalPresentationAmbientIso
import all Motivic.AlgebraicGeometry.SmoothSiteScalarPolynomialCoordinates
import all Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.LargePrimePolynomialZeroOriginalEtalePresentation
import all Motivic.AlgebraicGeometry.SmoothSiteScalarPolynomialPuncture
import all Motivic.AlgebraicGeometry.ScalarPolynomialOriginalPresentation
import all Motivic.AlgebraicGeometry.ScalarPolynomialZeroFiber
import all Motivic.AlgebraicGeometry.LargePrimeNativePolynomialPresentation
import all Motivic.AlgebraicGeometry.SmoothSiteScalarPolynomialOverlap
import all Motivic.AlgebraicGeometry.SmoothSiteScalarEtalePullback
import all Motivic.AlgebraicGeometry.PresheavesWithTransfers.FiniteScalarAffineCorrectionRestriction
import all Motivic.AlgebraicGeometry.SmoothSiteFiniteScalarOpenFactor
import all Motivic.Cohomology.A1.PresheafBoundaryOriginalOpenRefinement
import all Motivic.Cohomology.A1.PresheafBoundaryFinitePolynomialImage
import all Motivic.Cohomology.A1.FinitePresheafContractionBoundaryEpi
import all Motivic.Cohomology.A1.StrictInvarianceFiniteField
import Mathlib.Tactic.Linter
import Mathlib.Tactic.Linter.TextBased

/-! # Actual finite canonical boundary and ordinary strict-invariance consumers

The boundary test has arbitrary original PST coefficients and no HasExt premise.
Only the ordinary cohomological consumer assumes HasExt. Neither test supplies a
geometric theorem family.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry Motivic

universe u

namespace MotivicTest.FiniteCanonicalBoundaryStrictConsumer

variable {k : Type u} [Field k] [Finite k]

/-- The unchanged arbitrary original HI presheaf has the literal canonical Epi. -/
theorem original_boundary_epi (X : SmoothSite (Spec (.of k)))
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) :
    Epi (FiniteEtaleSite.OriginalPresheaf.contractionToBoundary X P) :=
  FiniteEtaleSite.OriginalPresheaf.contractionToBoundary_epi_of_finite X P hP

/-- Both geometric inputs are actual finite-field producers on the original map. -/
theorem original_projection_isIso
    [HasExt.{u + 1}
      (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant)
    (n : ℕ) (X : SmoothSite (Spec (.of k))) :
    IsIso (A1.projectionPullback (.of k)
      (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k)))
          ((SheafWithTransfers.toSheaf k).obj F) n) X) :=
  SheafWithTransfers.isStrictA1Invariant_of_finite F hF n X

open Lean Batteries.Tactic.Lint in
run_cmd do
  let env ← getEnv
  let sourceModules := #[
    `Motivic.AlgebraicGeometry.SmoothSiteAffineWeilRefinement,
    `Motivic.Cohomology.A1.OriginalPresentationAffineCombinedCorrection,
    `Motivic.AlgebraicGeometry.AffineCorrectionBaseRestriction,
    `Motivic.Aglib.AlgebraicGeometry.RelativeCurve.OriginalPresentationAmbientIso,
    `Motivic.AlgebraicGeometry.SmoothSiteScalarPolynomialCoordinates,
    `Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.LargePrimePolynomialZeroOriginalEtalePresentation,
    `Motivic.AlgebraicGeometry.SmoothSiteScalarPolynomialPuncture,
    `Motivic.AlgebraicGeometry.ScalarPolynomialOriginalPresentation,
    `Motivic.AlgebraicGeometry.ScalarPolynomialZeroFiber,
    `Motivic.AlgebraicGeometry.LargePrimeNativePolynomialPresentation,
    `Motivic.AlgebraicGeometry.SmoothSiteScalarPolynomialOverlap,
    `Motivic.AlgebraicGeometry.SmoothSiteScalarEtalePullback,
    `Motivic.AlgebraicGeometry.PresheavesWithTransfers.FiniteScalarAffineCorrectionRestriction,
    `Motivic.AlgebraicGeometry.SmoothSiteFiniteScalarOpenFactor,
    `Motivic.Cohomology.A1.PresheafBoundaryOriginalOpenRefinement,
    `Motivic.Cohomology.A1.PresheafBoundaryFinitePolynomialImage,
    `Motivic.Cohomology.A1.FinitePresheafContractionBoundaryEpi,
    `Motivic.Cohomology.A1.StrictInvarianceFiniteField]
  let modules := env.header.moduleNames.map (sourceModules.contains ·)
  let declarations := env.constants.map₁.fold
    (init := ← Lean.Elab.Command.liftCoreM getDeclsInCurrModule) fun declarations name _ =>
      if modules[env.const2ModIdx[name]?.get!]! then declarations.push name else declarations
  unless declarations.size ≥ 40 do
    throwError "Exact-origin actual finite strict invariance declarations are missing."
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
  let modules := #[
    `Motivic.AlgebraicGeometry.SmoothSiteAffineWeilRefinement,
    `Motivic.Cohomology.A1.OriginalPresentationAffineCombinedCorrection,
    `Motivic.AlgebraicGeometry.AffineCorrectionBaseRestriction,
    `Motivic.Aglib.AlgebraicGeometry.RelativeCurve.OriginalPresentationAmbientIso,
    `Motivic.AlgebraicGeometry.SmoothSiteScalarPolynomialCoordinates,
    `Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.LargePrimePolynomialZeroOriginalEtalePresentation,
    `Motivic.AlgebraicGeometry.SmoothSiteScalarPolynomialPuncture,
    `Motivic.AlgebraicGeometry.ScalarPolynomialOriginalPresentation,
    `Motivic.AlgebraicGeometry.ScalarPolynomialZeroFiber,
    `Motivic.AlgebraicGeometry.LargePrimeNativePolynomialPresentation,
    `Motivic.AlgebraicGeometry.SmoothSiteScalarPolynomialOverlap,
    `Motivic.AlgebraicGeometry.SmoothSiteScalarEtalePullback,
    `Motivic.AlgebraicGeometry.PresheavesWithTransfers.FiniteScalarAffineCorrectionRestriction,
    `Motivic.AlgebraicGeometry.SmoothSiteFiniteScalarOpenFactor,
    `Motivic.Cohomology.A1.PresheafBoundaryOriginalOpenRefinement,
    `Motivic.Cohomology.A1.PresheafBoundaryFinitePolynomialImage,
    `Motivic.Cohomology.A1.FinitePresheafContractionBoundaryEpi,
    `Motivic.Cohomology.A1.StrictInvarianceFiniteField,
    `MotivicTest.FiniteCanonicalBoundaryStrictConsumer]
  let errors ← lintModules options #[] modules .humanReadable false
  let casingErrors ← modulesNotUpperCamelCase options modules
  let filenameErrors ← modulesOSForbidden options modules
  unless errors == 0 && casingErrors == 0 && filenameErrors == 0 do
    throwError "Exact-file source text/style checks failed."
  logInfo "Pinned text/style checks passed for all nineteen selected modules."


end MotivicTest.FiniteCanonicalBoundaryStrictConsumer
