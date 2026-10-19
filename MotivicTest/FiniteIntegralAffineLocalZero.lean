/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.LocalVanishing.FiniteField.IntegralAffineLocalZero
public import Motivic.Cohomology.A1.LocalVanishing.Coefficient
import all Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.BaseChange.FiniteScalarMarkedOpen
import all Motivic.Transfers.Presheaf.FiniteScalarLocalZero
import all Motivic.Cohomology.A1.LocalVanishing.Presentation.OriginalOpen
import all Motivic.Cohomology.A1.LocalVanishing.FiniteField.ScalarPresentationLocalZero
import all Motivic.Cohomology.A1.LocalVanishing.FiniteField.AffineLocalVanishing
import all Motivic.Cohomology.A1.LocalVanishing.FiniteField.IntegralAffineLocalZero
import Mathlib.Tactic.Linter
import Mathlib.Tactic.Linter.TextBased

/-! # Actual finite-field integral-affine local-zero consumers

The section is original and the coefficient universe is arbitrary. No closed-point,
positive-dimension, scalar-zero or presentation-family premise is supplied.
The second consumer specializes this actual theorem to the upper D contract.
-/

public noncomputable section
open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory AlgebraicGeometry Motivic
universe u w
namespace MotivicTest.FiniteIntegralAffineLocalZero

/-- Every original point receives an affine zero neighborhood, at arbitrary coefficient size. -/
theorem original_affine_zero_neighborhood
    {k : Type u} [Field k] [Finite k]
    {X A : SmoothSite (Spec (.of k))} [IsAffine X.left] [IsIntegral X.left]
    [Nonempty A.left] (a : A ⟶ X) [IsOpenImmersion a.left]
    (P : PresheafWithTransfers.{w} k) (hP : P.IsA1Invariant)
    (v : P.sections (Cor.mk X)) (hv : P.transfer ((Cor.graphFunctor k).map a) v = 0)
    (x : X.left) :
    ∃ (O : X.left.Opens) (hO : IsAffineOpen O), x ∈ O ∧
      let : IsAffine O.toScheme := hO
      P.transfer ((Cor.graphFunctor k).map
        (SmoothSite.homMk (X := SmoothSite.mk (O.ι ≫ X.hom)) (Y := X) O.ι rfl)) v = 0 :=
  PresheafWithTransfers.exists_finite_zero_neighborhood_of_integral_affine a P hP v hv x

/-- The actual finite-field producer fills precisely the existing upper D contract. -/
theorem actual_integralAffineLocalZero (k : Type u) [Field k] [Finite k] :
    PresheafWithTransfers.IntegralAffineLocalZero k := by
  intro X A _ _ _ a _ P hP v hv x
  exact PresheafWithTransfers.exists_finite_zero_neighborhood_of_integral_affine a P hP v hv x

open Lean Batteries.Tactic.Lint in
run_cmd do
  let env ← getEnv
  let sourceModules := #[
    `Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.BaseChange.FiniteScalarMarkedOpen,
    `Motivic.Transfers.Presheaf.FiniteScalarLocalZero,
    `Motivic.Cohomology.A1.LocalVanishing.Presentation.OriginalOpen,
    `Motivic.Cohomology.A1.LocalVanishing.FiniteField.ScalarPresentationLocalZero,
    `Motivic.Cohomology.A1.LocalVanishing.FiniteField.AffineLocalVanishing,
    `Motivic.Cohomology.A1.LocalVanishing.FiniteField.IntegralAffineLocalZero]
  let modules := env.header.moduleNames.map (sourceModules.contains ·)
  let declarations := env.constants.map₁.fold
    (init := ← Lean.Elab.Command.liftCoreM getDeclsInCurrModule) fun declarations name _ =>
      if modules[env.const2ModIdx[name]?.get!]! then declarations.push name else declarations
  unless declarations.size ≥ 15 do
    throwError "Exact-origin finite local-zero declarations are missing."
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
    `Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.BaseChange.FiniteScalarMarkedOpen,
    `Motivic.Transfers.Presheaf.FiniteScalarLocalZero,
    `Motivic.Cohomology.A1.LocalVanishing.Presentation.OriginalOpen,
    `Motivic.Cohomology.A1.LocalVanishing.FiniteField.ScalarPresentationLocalZero,
    `Motivic.Cohomology.A1.LocalVanishing.FiniteField.AffineLocalVanishing,
    `Motivic.Cohomology.A1.LocalVanishing.FiniteField.IntegralAffineLocalZero,
    `MotivicTest.FiniteIntegralAffineLocalZero]
  let errors ← lintModules options #[] modules .humanReadable false
  let casingErrors ← modulesNotUpperCamelCase options modules
  let filenameErrors ← modulesOSForbidden options modules
  unless errors == 0 && casingErrors == 0 && filenameErrors == 0 do
    throwError "Exact-file source text/style checks failed."
  logInfo "Pinned text/style checks passed for all seven selected modules."


end MotivicTest.FiniteIntegralAffineLocalZero
