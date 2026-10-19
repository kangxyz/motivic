/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.FiniteSeparableExtension
import all Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.ForgetBase
import all Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.BaseChange.ForgetBaseA1
import all Motivic.AlgebraicGeometry.Correspondences.BaseChange.Forget.Support
import all Motivic.AlgebraicGeometry.Correspondences.BaseChange.Forget.Incidence
import all Motivic.AlgebraicGeometry.Correspondences.BaseChange.Forget.IncidenceTor
import all Motivic.AlgebraicGeometry.Correspondences.BaseChange.Forget.Cycle
import all Motivic.AlgebraicGeometry.Correspondences.BaseChange.Forget.Composition
import all Motivic.AlgebraicGeometry.Correspondences.BaseChange.Forget.Graph
import all Motivic.AlgebraicGeometry.Correspondences.BaseChange.FiniteSeparableForget
import all Motivic.Transfers.Presheaf.FiniteSeparableExtension
import Mathlib.Tactic.Linter.TextBased
import Lean.Util.CollectAxioms
import Batteries.Tactic.Lint

/-!
# Original coefficients and genuine homotopies over a finite separable extension

The consumer keeps the original arbitrary-universe P over k. It exercises
actual signed maps, composition, original graph restrictions and projection,
and transports a genuine L-correspondence homotopy back to P. No strict
invariance, ordinary cohomology comparison or sheaf premise is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory AlgebraicGeometry Motivic
open _root_.AlgebraicSimplex _root_.Motivic.PresheafWithTransfers

universe v u

namespace MotivicTest.FiniteSeparableCoefficients

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  [Module.Finite k L] [Algebra.IsSeparable k L]

/-- No coefficient group or coefficient universe is replaced. -/
theorem originalValues (P : PresheafWithTransfers.{v} k) (X : Cor L) :
    sections (finiteSeparableExtension L P) X =
      sections P ((Cor.finiteSeparableForgetBase k L).obj X) := rfl

/-- Every signed correspondence acts by the original P on its actual forgotten support. -/
theorem originalSignedAction (P : PresheafWithTransfers.{v} k) {X Y : Cor L} (α : X ⟶ Y) :
    transfer (finiteSeparableExtension L P) α =
      transfer P ((Cor.finiteSeparableForgetBase k L).map α) := rfl

/-- Actual Tor composition, not an assumed external category law, is preserved. -/
theorem originalComposition {X Y Z : Cor L} (α : X ⟶ Y) (β : Y ⟶ Z) :
    (Cor.finiteSeparableForgetBase k L).map (α ≫ β) =
      (Cor.finiteSeparableForgetBase k L).map α ≫ (Cor.finiteSeparableForgetBase k L).map β :=
  (Cor.finiteSeparableForgetBase k L).map_comp α β

/-- The exact original coefficient projection over L is invertible from original P-HI. -/
theorem originalProjection (P : PresheafWithTransfers.{v} k) (hP : P.IsA1Invariant)
    (X : SmoothSite (Spec (.of L))) :
    IsIso (transfer P ((Cor.graphFunctor k).map
      ((SmoothSite.finiteSeparableForgetBase k L).map (SmoothSite.a1Projection (.of L) X)))) := by
  have h := finiteSeparableExtension_isA1Invariant L P hP X
  change IsIso (transfer (finiteSeparableExtension L P)
    ((Cor.graphFunctor L).map (SmoothSite.a1Projection (.of L) X))) at h
  simpa only [finiteSeparableExtension_transfer, Cor.finiteSeparableForgetBase_graph] using h

/-- Genuine homotopies over L act equally at both original endpoints on the same P over k.
The endpoint scalars may be arbitrary elements of L, not only images of k. -/
theorem originalHomotopyEndpoints (P : PresheafWithTransfers.{v} k) (hP : P.IsA1Invariant)
    (X : SmoothSite (Spec (.of L))) (Y : Cor L)
    (α : Cor.mk (SmoothSite.a1Cylinder (.of L) X) ⟶ Y) (a b : L) :
    transfer P ((Cor.graphFunctor k).map
        ((SmoothSite.finiteSeparableForgetBase k L).map (SmoothSite.a1Section (.of L) X a)) ≫
          (Cor.finiteSeparableForgetBase k L).map α) =
      transfer P ((Cor.graphFunctor k).map
        ((SmoothSite.finiteSeparableForgetBase k L).map (SmoothSite.a1Section (.of L) X b)) ≫
          (Cor.finiteSeparableForgetBase k L).map α) := by
  have h := transfer_homotopy_endpoints (finiteSeparableExtension L P)
    (finiteSeparableExtension_isA1Invariant L P hP) X Y α a b
  simpa only [finiteSeparableExtension_transfer, Functor.map_comp,
    Cor.finiteSeparableForgetBase_graph] using h

open Lean Batteries.Tactic.Lint in
run_cmd do
  let env ← getEnv
  let sourceModules := #[
    `Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.ForgetBase,
    `Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.BaseChange.ForgetBaseA1,
    `Motivic.AlgebraicGeometry.Correspondences.BaseChange.Forget.Support,
    `Motivic.AlgebraicGeometry.Correspondences.BaseChange.Forget.Incidence,
    `Motivic.AlgebraicGeometry.Correspondences.BaseChange.Forget.IncidenceTor,
    `Motivic.AlgebraicGeometry.Correspondences.BaseChange.Forget.Cycle,
    `Motivic.AlgebraicGeometry.Correspondences.BaseChange.Forget.Composition,
    `Motivic.AlgebraicGeometry.Correspondences.BaseChange.Forget.Graph,
    `Motivic.AlgebraicGeometry.Correspondences.BaseChange.FiniteSeparableForget,
    `Motivic.Transfers.Presheaf.FiniteSeparableExtension]
  let modules := env.header.moduleNames.map (sourceModules.contains ·)
  let declarations := env.constants.map₁.fold
    (init := ← Lean.Elab.Command.liftCoreM getDeclsInCurrModule) fun declarations name _ =>
      if modules[env.const2ModIdx[name]?.get!]! then declarations.push name else declarations
  unless declarations.size ≥ 80 do
    throwError "The exact finite separable coefficient declarations are missing."
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
  logInfo m!"Original finite separable coefficients: {declarations.size} declarations passed."

open Lean Mathlib.Linter.TextBased in
run_cmd do
  let options : Lean.Linter.LinterOptions := {
    toOptions := ← getOptions
    linterSets := (Lean.Linter.linterSetsExt.getState (← getEnv)).merged }
  let modules := #[
    `Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.ForgetBase,
    `Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.BaseChange.ForgetBaseA1,
    `Motivic.AlgebraicGeometry.Correspondences.BaseChange.Forget.Support,
    `Motivic.AlgebraicGeometry.Correspondences.BaseChange.Forget.Incidence,
    `Motivic.AlgebraicGeometry.Correspondences.BaseChange.Forget.IncidenceTor,
    `Motivic.AlgebraicGeometry.Correspondences.BaseChange.Forget.Cycle,
    `Motivic.AlgebraicGeometry.Correspondences.BaseChange.Forget.Composition,
    `Motivic.AlgebraicGeometry.Correspondences.BaseChange.Forget.Graph,
    `Motivic.AlgebraicGeometry.Correspondences.BaseChange.FiniteSeparableForget,
    `Motivic.Transfers.Presheaf.FiniteSeparableExtension,
    `MotivicTest.FiniteSeparableCoefficients]
  let errors ← lintModules options #[] modules .humanReadable false
  let casingErrors ← modulesNotUpperCamelCase options modules
  let filenameErrors ← modulesOSForbidden options modules
  unless errors == 0 && casingErrors == 0 && filenameErrors == 0 do
    throwError "Finite separable coefficient text/style checks failed."
  logInfo "Pinned Lean text/style passed for eleven exact finite separable coefficient sources."

end MotivicTest.FiniteSeparableCoefficients
