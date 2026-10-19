/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.Divisors.GraphIdealMoved
import all Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.Prescribed.OpenRangeFrame
import all Motivic.Aglib.AlgebraicGeometry.Cycles.Divisors.GraphIdealMoved
public import Lean.Util.CollectAxioms
public import Batteries.Tactic.Lint
public import Mathlib.Tactic.Linter.TextBased

/-!
# Original compactification graph with prescribed moved support

The actual graph ideal, canonical infinity frame, marked split frame and exact
affine extension feed the literal moved sum. Integral and nonempty-boundary
hypotheses remain explicit; this does not assert a principal A1 relation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible Scheme.Hom

universe u

namespace MotivicTest.GraphIdealMovedCycle


variable {S C T D Z : Scheme.{u}} (q : C ⟶ S) [IsProper q]
  (j : T ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ q)]
  (d : D ⟶ C) (z : Z ⟶ C)
  (hd : Disjoint (Set.range j) (Set.range d))
  (eZ : (Scheme.Modules.pullback (infinityProductMap q j z)).obj
      (idealModule (compactificationGraph q j)) ≅
    SheafOfModules.unit (pullback (pullback.snd (j ≫ q) q) z).ringCatSheaf)

variable (A : (pullback (j ≫ q) q).affineOpens)
  (b : (pullback (pullback.snd (j ≫ q) q) d ⨿
    pullback (pullback.snd (j ≫ q) q) z) ⟶ A.val.toScheme)
  (hb : b ≫ A.val.ι =
    coprod.desc (infinityProductMap q j d) (infinityProductMap q j z))

/-- The original graph plus the native order of its boundary-frame ratio has
whole support finite over the unchanged parameter. All frame-extension data,
including the exact prescribed restriction, are retained in the witness. -/
theorem original_graph_prescribed_moved_support
    [IsAffine T] [IsIntegral (pullback (j ≫ q) q)]
    [IsNoetherian (pullback (j ≫ q) q)]
    [IsClosedImmersion b]
    [Nonempty ((pullback (pullback.snd (j ≫ q) q) d ⨿
      pullback (pullback.snd (j ≫ q) q) z) : Scheme.{u})]
    {V : Scheme.{u}} [V.IsQuasiAffine]
    (v : V ⟶ pullback (j ≫ q) q) [IsOpenImmersion v]
    (hboundary : (Set.range v)ᶜ ⊆ Set.range
      (coprod.desc (infinityProductMap q j d) (infinityProductMap q j z))) :
    ∃ E : PrescribedAffineFrameExtension A b (relativeCompactificationGraphLine q j)
        (_root_.AlgebraicGeometry.Scheme.Cycles.GraphDivisorPencil.affineBoundaryFrame q j d z hd eZ
            A b hb),
      (∀ x ∈ E.affineOpen.val,
        _root_.AlgebraicGeometry.Scheme.idealFrameMovedCycle (compactificationGraph q j)
            E.affineOpen E.overFrame
          1 isUnit_one x = 0) ∧
      (∀ x, _root_.AlgebraicGeometry.Scheme.idealFrameMovedCycle (compactificationGraph q j)
          E.affineOpen E.overFrame
          1 isUnit_one x ≠ 0 →
        IsFinite ((_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure
            x).val.subschemeι ≫
          pullback.fst (j ≫ q) q)) :=
  _root_.AlgebraicGeometry.Scheme.Cycles.GraphDivisorPencil.exists_original_graph_moved_sum q j d z
      hd eZ A b hb v hboundary

open Lean Batteries.Tactic.Lint in
run_cmd do
  let env ← getEnv
  let sourceModules := #[
    `Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.Prescribed.OpenRangeFrame,
    `Motivic.Aglib.AlgebraicGeometry.Cycles.Divisors.GraphIdealMoved]
  let modules := env.header.moduleNames.map (sourceModules.contains ·)
  let declarations := env.constants.map₁.fold
    (init := ← Lean.Elab.Command.liftCoreM getDeclsInCurrModule) fun declarations name _ =>
      if modules[env.const2ModIdx[name]?.get!]! then declarations.push name else declarations
  unless declarations.size ≥ 15 do
    throwError "Exact-origin original graph moved-support declarations are missing."
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
    `Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.Prescribed.OpenRangeFrame,
    `Motivic.Aglib.AlgebraicGeometry.Cycles.Divisors.GraphIdealMoved,
    `MotivicTest.GraphIdealMovedCycle]
  let errors ← lintModules options #[] modules .humanReadable false
  let casingErrors ← modulesNotUpperCamelCase options modules
  let filenameErrors ← modulesOSForbidden options modules
  unless errors == 0 && casingErrors == 0 && filenameErrors == 0 do
    throwError "Exact-file source text/style checks failed."
  logInfo "Pinned text/style checks passed for all three selected modules."

end MotivicTest.GraphIdealMovedCycle
