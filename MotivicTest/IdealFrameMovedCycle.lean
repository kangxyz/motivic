/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.Divisors.Frame.MovedCycle
import all Motivic.Aglib.AlgebraicGeometry.Divisors.Order.PrincipalOrderCancellation
import all Motivic.Aglib.AlgebraicGeometry.Divisors.Order.IdealFrameOrderCancellation
import all Motivic.Aglib.AlgebraicGeometry.Cycles.Divisors.Frame.Cancellation
import all Motivic.Aglib.AlgebraicGeometry.Cycles.Divisors.Frame.Support
import all Motivic.Aglib.AlgebraicGeometry.Cycles.Divisors.Frame.MovedCycle
public import Lean.Util.CollectAxioms
public import Batteries.Tactic.Lint
public import Mathlib.Tactic.Linter.TextBased

/-!
# Original moved-cycle support consumer

This checks the literal fundamental cycle plus native principal orders and whole
support finiteness. A prescribed ideal frame remains an explicit geometric input.
No graph specialization, frame existence, or principal A1 relation is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible Scheme.Hom

universe u

namespace MotivicTest.IdealFrameMovedCycle

/-- The literal moved sum vanishes on the entire prescribed frame neighborhood,
and every surviving whole integral support is finite over the unchanged base. -/
theorem original_sum_boundary_avoidance_and_finiteness
    {C D S V : Scheme.{u}} [IsIntegral C] [IsNoetherian C]
    (i : D ⟶ C) [IsClosedImmersion i]
    (hI : IsLocallyRankOne C (idealModule i))
    (W : C.affineOpens) [Nonempty W.val]
    (e : (idealModule i).over W.val ≅ SheafOfModules.unit (C.ringCatSheaf.over W.val))
    (b : Γ(C, W.val)) (hb : IsUnit b)
    [IsAffine S] [V.IsQuasiAffine] (q : C ⟶ S) [IsProper q]
    (j : V ⟶ C) [IsOpenImmersion j]
    (hW : (Set.range j)ᶜ ⊆ (W.val : Set C)) :
    (∀ x ∈ W.val, _root_.AlgebraicGeometry.Scheme.idealFrameMovedCycle i W e b hb x = 0) ∧
      (∀ x, _root_.AlgebraicGeometry.Scheme.idealFrameMovedCycle i W e b hb x ≠ 0 →
        closure ({x} : Set C) ⊆ (W.val : Set C)ᶜ ∧
          IsFinite ((_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure
              x).val.subschemeι ≫ q)) := by
  refine ⟨fun _ hx => _root_.AlgebraicGeometry.Scheme.idealFrameMovedCycle_eq_zero_on_frame i W e b
      hb hI hx, ?_⟩
  intro x hx
  exact ⟨_root_.AlgebraicGeometry.Scheme.idealFrameMovedCycle_support_closure i W e b hb hI x hx,
    _root_.AlgebraicGeometry.Scheme.idealFrameMovedCycle_support_isFinite i W e b hb hI q j hW x hx⟩

open Lean Batteries.Tactic.Lint in
run_cmd do
  let env ← getEnv
  let sourceModules := #[
    `Motivic.Aglib.AlgebraicGeometry.Divisors.Order.PrincipalOrderCancellation,
    `Motivic.Aglib.AlgebraicGeometry.Divisors.Order.IdealFrameOrderCancellation,
    `Motivic.Aglib.AlgebraicGeometry.Cycles.Divisors.Frame.Cancellation,
    `Motivic.Aglib.AlgebraicGeometry.Cycles.Divisors.Frame.Support,
    `Motivic.Aglib.AlgebraicGeometry.Cycles.Divisors.Frame.MovedCycle]
  let modules := env.header.moduleNames.map (sourceModules.contains ·)
  let declarations := env.constants.map₁.fold
    (init := ← Lean.Elab.Command.liftCoreM getDeclsInCurrModule) fun declarations name _ =>
      if modules[env.const2ModIdx[name]?.get!]! then declarations.push name else declarations
  unless declarations.size ≥ 18 do
    throwError "Exact-origin original moved-cycle declarations are missing."
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
    `Motivic.Aglib.AlgebraicGeometry.Divisors.Order.PrincipalOrderCancellation,
    `Motivic.Aglib.AlgebraicGeometry.Divisors.Order.IdealFrameOrderCancellation,
    `Motivic.Aglib.AlgebraicGeometry.Cycles.Divisors.Frame.Cancellation,
    `Motivic.Aglib.AlgebraicGeometry.Cycles.Divisors.Frame.Support,
    `Motivic.Aglib.AlgebraicGeometry.Cycles.Divisors.Frame.MovedCycle,
    `MotivicTest.IdealFrameMovedCycle]
  let errors ← lintModules options #[] modules .humanReadable false
  let casingErrors ← modulesNotUpperCamelCase options modules
  let filenameErrors ← modulesOSForbidden options modules
  unless errors == 0 && casingErrors == 0 && filenameErrors == 0 do
    throwError "Exact-file source text/style checks failed."
  logInfo "Pinned text/style checks passed for all six selected modules."

end MotivicTest.IdealFrameMovedCycle
