/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.FiniteScalarComparisonDifference
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.BaseChange.FieldBaseChangeA1
public import Motivic.Cohomology.A1.LocalVanishing.RelativeCurve.LocalLifting
import all Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.BaseChange.FiniteScalarComparison
import all Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.BaseChange.FieldBaseChangeA1
import all Motivic.Transfers.Presheaf.FiniteScalarComparison
import all Motivic.Transfers.Presheaf.FiniteScalarComparisonDifference
import Mathlib.Tactic.Linter.TextBased
import Lean.Util.CollectAxioms
import Batteries.Tactic.Lint

/-! # Original extended-coefficient lifting and actual coprime traces -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory AlgebraicGeometry Motivic
open _root_.AlgebraicSimplex _root_.Motivic.PresheafWithTransfers

universe u

namespace MotivicTest.FiniteScalarCoefficientMaps

variable {k E L : Type u} [Field k] [Field E] [Field L]
  [Algebra k E] [Module.Finite k E] [Algebra.IsSeparable k E]
  [Algebra k L] [Module.Finite k L] [Algebra.IsSeparable k L]

/-- Actual extended-coefficient lifting descends on one original correction diagram.
Neither a replacement coefficient nor an abstract scalar trace is supplied. -/
theorem originalRestrictionDifference (P : PresheafWithTransfers.{u + 1} k)
    {O T A D : SmoothSite (Spec (.of k))}
    (β : O ⟶ T) [Flat β.left] (α : O ⟶ A) [Flat α.left] (φ : O ⟶ D)
    (hE : HasRestrictionDifferenceLifting (finiteSeparableExtension E P)
      ((SmoothSite.fieldBaseChange (algebraMap k E)).map φ)
      ((SmoothSite.fieldBaseChange (algebraMap k E)).map β)
      ((SmoothSite.fieldBaseChange (algebraMap k E)).map α))
    (hL : HasRestrictionDifferenceLifting (finiteSeparableExtension L P)
      ((SmoothSite.fieldBaseChange (algebraMap k L)).map φ)
      ((SmoothSite.fieldBaseChange (algebraMap k L)).map β)
      ((SmoothSite.fieldBaseChange (algebraMap k L)).map α))
    (hdegree : (Module.finrank k E).Coprime (Module.finrank k L)) :
    HasRestrictionDifferenceLifting P φ β α := by
  intro s
  obtain ⟨aE, cE, he⟩ := hE (transfer P ((Cor.graphFunctor k).map
    (SmoothSite.fieldBaseChangeForgetProjection (L := E) D)) s)
  obtain ⟨aL, cL, hl⟩ := hL (transfer P ((Cor.graphFunctor k).map
    (SmoothSite.fieldBaseChangeForgetProjection (L := L) D)) s)
  exact exists_restriction_difference_of_coprime_finiteScalar P β α φ s
    ⟨(finiteScalarSectionIso (L := E) P T).hom aE,
      (finiteScalarSectionIso (L := E) P A).hom cE,
      finiteScalarSectionIso_restriction_difference P β α φ s aE cE he⟩
    ⟨(finiteScalarSectionIso (L := L) P T).hom aL,
      (finiteScalarSectionIso (L := L) P A).hom cL,
      finiteScalarSectionIso_restriction_difference P β α φ s aL cL hl⟩ hdegree

omit [Module.Finite k L] [Algebra.IsSeparable k L] in
/-- The native zero section is identified by the actual field-change comparison. -/
theorem originalZeroSection (X : SmoothSite (Spec (.of k))) :
    (SmoothSite.fieldBaseChange (algebraMap k L)).map (SmoothSite.a1Section (.of k) X 0) ≫
        (SmoothSite.fieldBaseChangeA1Iso (L := L) X).hom =
      SmoothSite.a1Section (.of L) ((SmoothSite.fieldBaseChange (algebraMap k L)).obj X) 0 :=
  SmoothSite.fieldBaseChangeA1Iso_zero X

omit [Module.Finite k L] [Algebra.IsSeparable k L] in
/-- The exact Laurent-open arrow used in the signed boundary relation is preserved. -/
theorem originalLaurentOpen (X : SmoothSite (Spec (.of k))) :
    (SmoothSite.fieldBaseChange (algebraMap k L)).map (SmoothSite.contractionOpen (.of k) X) ≫
        (SmoothSite.fieldBaseChangeA1Iso (L := L) X).hom =
      (SmoothSite.fieldBaseChangeTorusCylinderIso (L := L) X).hom ≫
        SmoothSite.contractionOpen (.of L)
          ((SmoothSite.fieldBaseChange (algebraMap k L)).obj X) :=
  SmoothSite.fieldBaseChangeA1Iso_contractionOpen X

open Lean Batteries.Tactic.Lint in
run_cmd do
  let env ← getEnv
  let sourceModules := #[
    `Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.BaseChange.FiniteScalarComparison,
    `Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.BaseChange.FieldBaseChangeA1,
    `Motivic.Transfers.Presheaf.FiniteScalarComparison,
    `Motivic.Transfers.Presheaf.FiniteScalarComparisonDifference]
  let modules := env.header.moduleNames.map (sourceModules.contains ·)
  let declarations := env.constants.map₁.fold
    (init := ← Lean.Elab.Command.liftCoreM getDeclsInCurrModule) fun declarations name _ =>
      if modules[env.const2ModIdx[name]?.get!]! then declarations.push name else declarations
  unless declarations.size ≥ 20 do
    throwError "The exact finite scalar coefficient map declarations are missing."
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
  logInfo m!"Original finite scalar coefficient maps: {declarations.size} declarations passed."

open Lean Mathlib.Linter.TextBased in
run_cmd do
  let options : Lean.Linter.LinterOptions := {
    toOptions := ← getOptions
    linterSets := (Lean.Linter.linterSetsExt.getState (← getEnv)).merged }
  let modules := #[
    `Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.BaseChange.FiniteScalarComparison,
    `Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.BaseChange.FieldBaseChangeA1,
    `Motivic.Transfers.Presheaf.FiniteScalarComparison,
    `Motivic.Transfers.Presheaf.FiniteScalarComparisonDifference,
    `MotivicTest.FiniteScalarCoefficientMaps]
  let errors ← lintModules options #[] modules .humanReadable false
  let casingErrors ← modulesNotUpperCamelCase options modules
  let filenameErrors ← modulesOSForbidden options modules
  unless errors == 0 && casingErrors == 0 && filenameErrors == 0 do
    throwError "Finite scalar coefficient map text/style checks failed."
  logInfo "Pinned Lean text/style passed for five exact finite scalar coefficient map sources."

end MotivicTest.FiniteScalarCoefficientMaps
