/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.PointedCartierH1Restriction
public import Motivic.Cohomology.SheafCohomologyCartierVanishing
import all Motivic.Cohomology.A1.ContractionBoundaryIso
import all Motivic.Cohomology.A1.PointedCartierH1Restriction
import all Motivic.Cohomology.SheafCohomologyCartierVanishing
import all Motivic.Aglib.AlgebraicGeometry.RelativeCurve.PresentationMissingBoundary
import all Motivic.Cohomology.A1.OriginalEtalePresentationLifting
import all Motivic.Cohomology.A1.PresentationLocalVanishing
import Mathlib.Tactic.Linter.TextBased
import Lean.Util.CollectAxioms
import Batteries.Tactic.Lint

/-! # Actual Cartier applications with the canonical boundary input discharged -/

public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace MotivicTest.CanonicalBoundaryApplications

/-- Original full-marked H1 injectivity, with no supplied canonical Epi. -/
theorem original_H1_cartier_puncture_injective
    (k : Type u) [Field k] [Infinite k]
    [HasExt.{u + 1}
      (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
    (Y : SmoothSite (Spec (.of k))) (F : SheafWithTransfers.{u + 1} k)
    (hF : F.obj.IsA1Invariant)
    {Z : Scheme.{u}} (i : Z ⟶ Y.left) [IsClosedImmersion i] [Smooth (i ≫ Y.hom)]
    (hI : IsLocallyRankOne Y.left (Scheme.Hom.idealModule i))
    {U : SmoothSite (Spec (.of k))} (j : U ⟶ Y) [IsOpenImmersion j.left]
    (hcomp : Set.range i = (Set.range j.left)ᶜ)
    (K : Type u) [Field K] (b : Spec (.of K) ⟶ Y.left) (s : Spec (.of K))
    (hb : b s ∈ Set.range i) :
    Function.Injective (colim.map (FiniteEtaleSite.pointedCylinderRestriction (.of k) j
      (FiniteEtaleSite.relativeFieldPoint b K (𝟙 _))
      (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k)))
          ((SheafWithTransfers.toSheaf k).obj F) 1))) := by
  apply (AddCommGrpCat.mono_iff_injective _).mp
  exact FiniteEtaleSite.pointedCylinderRestriction_H1_mono_of_cartier
    Y F hF i hI j hcomp K b s hb


/-- The actual higher open direct image uses only the specified degree's HI. -/
theorem original_higherDirectImage_isZero
    (k : Type u) [Field k] [Infinite k]
    [HasExt.{u + 1}
      (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
    (F : SheafWithTransfers.{u + 1} k) (n : ℕ)
    (hP : (SheafCohomology.withTransfers k F (n + 1)).IsA1Invariant)
    {U Y : SmoothSite (Spec (.of k))} (j : U ⟶ Y) [IsOpenImmersion j.left]
    {Z : Scheme.{u}} (i : Z ⟶ Y.left) [IsClosedImmersion i] [Smooth (i ≫ Y.hom)]
    (hI : IsLocallyRankOne Y.left (Scheme.Hom.idealModule i))
    (hcomp : Set.range i = (Set.range j.left)ᶜ) :
    IsZero (((FiniteEtaleSite.directImage j.left).rightDerived (n + 1)).obj
      ((FiniteEtaleSite.restrict U AddCommGrpCat).obj
        ((SheafWithTransfers.toSheaf k).obj F))) :=
  SheafCohomology.higherDirectImage_isZero_of_cartier k F n hP j i hI hcomp

open Lean Batteries.Tactic.Lint in
run_cmd do
  let env ← getEnv
  let sourceModules := #[`Motivic.Cohomology.A1.ContractionBoundaryIso,
    `Motivic.Cohomology.A1.PointedCartierH1Restriction,
    `Motivic.Cohomology.SheafCohomologyCartierVanishing,
    `Motivic.Aglib.AlgebraicGeometry.RelativeCurve.PresentationMissingBoundary,
    `Motivic.Cohomology.A1.OriginalEtalePresentationLifting,
    `Motivic.Cohomology.A1.PresentationLocalVanishing]
  let modules := env.header.moduleNames.map (sourceModules.contains ·)
  let declarations := env.constants.map₁.fold
    (init := ← Lean.Elab.Command.liftCoreM getDeclsInCurrModule) fun declarations name _ =>
      if modules[env.const2ModIdx[name]?.get!]! then declarations.push name else declarations
  unless declarations.size ≥ 7 do
    throwError "The actual canonical boundary applications are missing."
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
  logInfo m!"Canonical boundary applications: {declarations.size} declarations passed."

open Lean Mathlib.Linter.TextBased in
run_cmd do
  let options : Lean.Linter.LinterOptions := {
    toOptions := ← getOptions
    linterSets := (Lean.Linter.linterSetsExt.getState (← getEnv)).merged }
  let modules := #[`Motivic.Cohomology.A1.ContractionBoundaryIso,
    `Motivic.Cohomology.A1.PointedCartierH1Restriction,
    `Motivic.Cohomology.SheafCohomologyCartierVanishing,
    `Motivic.Aglib.AlgebraicGeometry.RelativeCurve.PresentationMissingBoundary,
    `Motivic.Cohomology.A1.OriginalEtalePresentationLifting,
    `Motivic.Cohomology.A1.PresentationLocalVanishing,
    `MotivicTest.CanonicalBoundaryApplications]
  let errors ← lintModules options #[] modules .humanReadable false
  let casingErrors ← modulesNotUpperCamelCase options modules
  let filenameErrors ← modulesOSForbidden options modules
  unless errors == 0 && casingErrors == 0 && filenameErrors == 0 do
    throwError "Canonical boundary applications text/style checks failed."
  logInfo "Pinned Lean text/style passed for seven exact application sources."

end MotivicTest.CanonicalBoundaryApplications
