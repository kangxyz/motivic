/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.Boundary.Presheaf.ScalarDescent
public import Motivic.Cohomology.A1.LocalVanishing.RelativeCurve.LocalLifting
import all Motivic.Transfers.Presheaf.FiniteScalarRestrictionDifference
import all Motivic.Cohomology.A1.Boundary.Presheaf.ScalarDescent
import Mathlib.Tactic.Linter.TextBased
import Lean.Util.CollectAxioms
import Batteries.Tactic.Lint

/-! # Original signed local lifting through actual coprime scalar traces

The actual scalar-extended lifting predicates yield the original lifting
predicate on one fixed geometric diagram. The canonical boundary image
consumer retains that same diagram and does not assert finite-field Epi.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open _root_.AlgebraicSimplex _root_.Motivic.PresheafWithTransfers

universe u

namespace MotivicTest.BoundaryScalarDescent

variable {k E L : Type u} [Field k] [Field E] [Field L]
  [Algebra k E] [Module.Finite k E] [Algebra.IsSeparable k E]
  [Algebra k L] [Module.Finite k L] [Algebra.IsSeparable k L]

/-- The geometric signed-lifting interface is preserved by actual coprime trace
on scalar extensions of one original diagram, with the original coefficient unchanged. -/
theorem originalRestrictionDifference (P : PresheafWithTransfers.{u + 1} k)
    {O T A D : SmoothSite (Spec (.of k))}
    (β : O ⟶ T) [Flat β.left] (α : O ⟶ A) [Flat α.left] (φ : O ⟶ D)
    (hE : HasRestrictionDifferenceLifting P
      (SmoothSite.finiteScalarMap (E := E) φ)
      (SmoothSite.finiteScalarMap (E := E) β)
      (SmoothSite.finiteScalarMap (E := E) α))
    (hL : HasRestrictionDifferenceLifting P
      (SmoothSite.finiteScalarMap (E := L) φ)
      (SmoothSite.finiteScalarMap (E := L) β)
      (SmoothSite.finiteScalarMap (E := L) α))
    (hdegree : (Module.finrank k E).Coprime (Module.finrank k L)) :
    HasRestrictionDifferenceLifting P φ β α := by
  intro s
  exact exists_restriction_difference_of_coprime_finiteScalar P β α φ s
    (hE (transfer P ((Cor.graphFunctor k).map
      (SmoothSite.finiteScalarProjection (E := E) D)) s))
    (hL (transfer P ((Cor.graphFunctor k).map
      (SmoothSite.finiteScalarProjection (E := L) D)) s)) hdegree

#check FiniteEtaleSite.OriginalPresheaf.imageSieve_of_coprime_finiteScalar_geometric_difference

open Lean Batteries.Tactic.Lint in
run_cmd do
  let env ← getEnv
  let sourceModules := #[`Motivic.Transfers.Presheaf.FiniteScalarRestrictionDifference,
    `Motivic.Cohomology.A1.Boundary.Presheaf.ScalarDescent]
  let modules := env.header.moduleNames.map (sourceModules.contains ·)
  let declarations := env.constants.map₁.fold
    (init := ← Lean.Elab.Command.liftCoreM getDeclsInCurrModule) fun declarations name _ =>
      if modules[env.const2ModIdx[name]?.get!]! then declarations.push name else declarations
  unless declarations.size ≥ 6 do
    throwError "The exact original scalar descent declarations are missing."
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
  logInfo m!"Original boundary scalar descent: {declarations.size} declarations passed."

open Lean Mathlib.Linter.TextBased in
run_cmd do
  let options : Lean.Linter.LinterOptions := {
    toOptions := ← getOptions
    linterSets := (Lean.Linter.linterSetsExt.getState (← getEnv)).merged }
  let modules := #[`Motivic.Transfers.Presheaf.FiniteScalarRestrictionDifference,
    `Motivic.Cohomology.A1.Boundary.Presheaf.ScalarDescent, `MotivicTest.BoundaryScalarDescent]
  let errors ← lintModules options #[] modules .humanReadable false
  let casingErrors ← modulesNotUpperCamelCase options modules
  let filenameErrors ← modulesOSForbidden options modules
  unless errors == 0 && casingErrors == 0 && filenameErrors == 0 do
    throwError "Finite scalar descent text/style checks failed."
  logInfo "Pinned Lean text/style passed for three exact boundary scalar descent sources."

end MotivicTest.BoundaryScalarDescent
