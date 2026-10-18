/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.ContractionBoundaryProjectionCompatibility
public import Motivic.Cohomology.A1.ContractionBoundaryMono
public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleA1Coefficient
import all Motivic.AlgebraicGeometry.SmoothSiteProductPermutation
import all Motivic.Cohomology.A1.ContractionBoundaryProjectionGeometry
import all Motivic.Cohomology.A1.ContractionBoundaryProjection
import all Motivic.Cohomology.A1.ContractionBoundaryProjectionCompatibility
import Lean.Util.CollectAxioms
import Batteries.Tactic.Lint

/-! # The actual boundary projection, conditional on the remaining canonical Epi inputs -/

set_option linter.hashCommand false

public noncomputable section

open CategoryTheory AlgebraicGeometry Motivic

universe u

namespace MotivicTest.ContractionBoundaryProjection

variable {k : Type u} [Field k] (X : SmoothSite (Spec (CommRingCat.of k)))
  (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant)

/-- Once the two explicitly displayed canonical Epi inputs are supplied, the
actual zero-section boundary projection is invertible by ordinary HI of the
unchanged contraction. Neither Epi input is discharged by this consumer. -/
theorem actual_projection_isIso
    (hE₀ : Epi (FiniteEtaleSite.contractionToBoundary X F hF))
    (hE₁ : Epi (FiniteEtaleSite.contractionToBoundary
      (SmoothSite.a1Cylinder (CommRingCat.of k) X) F hF)) :
    IsIso (FiniteEtaleSite.contractionBoundaryProjection X F) := by
  let := hE₀
  let := hE₁
  let := FiniteEtaleSite.contractionToBoundary_mono X F hF
  let := FiniteEtaleSite.contractionToBoundary_mono (SmoothSite.a1Cylinder (CommRingCat.of k) X) F hF
  let : IsIso (FiniteEtaleSite.contractionToBoundary X F hF) := isIso_of_mono_of_epi _
  let : IsIso (FiniteEtaleSite.contractionToBoundary
      (SmoothSite.a1Cylinder (CommRingCat.of k) X) F hF) := isIso_of_mono_of_epi _
  let H := (SheafWithTransfers.toSheaf k).obj (SheafWithTransfers.contraction F hF)
  let := FiniteEtaleSite.a1RestrictionCoefficient_isIso (CommRingCat.of k) X H
    (SheafWithTransfers.contraction_isA1Invariant F hF)
  let : IsIso (FiniteEtaleSite.contractionToBoundary X F hF ≫
      FiniteEtaleSite.contractionBoundaryProjection X F) := by
    rw [FiniteEtaleSite.contractionToBoundary_projection]
    infer_instance
  exact IsIso.of_isIso_comp_left (FiniteEtaleSite.contractionToBoundary X F hF) _

open Lean in
run_cmd do
  for dependency in ← collectAxioms ``actual_projection_isIso do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
      throwError "The actual boundary projection consumer depends on {dependency}"
  logInfo "Actual boundary projection: explicit canonical Epi inputs, standard axioms only."

open Lean Batteries.Tactic.Lint in
run_cmd do
  let env ← getEnv
  let sourceModules := #[`Motivic.AlgebraicGeometry.SmoothSiteProductPermutation,
    `Motivic.Cohomology.A1.ContractionBoundaryProjectionGeometry,
    `Motivic.Cohomology.A1.ContractionBoundaryProjection,
    `Motivic.Cohomology.A1.ContractionBoundaryProjectionCompatibility]
  let modules := env.header.moduleNames.map (sourceModules.contains ·)
  let declarations := env.constants.map₁.fold
    (init := ← Lean.Elab.Command.liftCoreM getDeclsInCurrModule) fun declarations name _ =>
      if modules[env.const2ModIdx[name]?.get!]! then declarations.push name else declarations
  unless declarations.size ≥ 25 do
    throwError "The actual projection declarations are missing from this lint."
  let linters ← Lean.Elab.Command.liftCoreM (getChecks true none none)
  unless !linters.isEmpty do
    throwError "No declaration linters were selected."
  let results ← Lean.Elab.Command.liftCoreM <|
    Lean.withExporting (isExporting := false) (lintCore declarations linters)
  for (linter, findings) in results do
    for (name, message) in findings.toArray do
      throwError "{linter.name}: {name}: {message}"
  logInfo m!"Actual projection comparison: {declarations.size} declarations passed lint."

end MotivicTest.ContractionBoundaryProjection
