/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.FixedParameterBoundaryNeighborhood
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.OriginalAffinePrescribedNeighborhood
public import Motivic.AlgebraicGeometry.SmoothSite
import all Motivic.Aglib.AlgebraicGeometry.RelativeCurve.FixedParameterBoundaryNeighborhood
import all Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.AffinePrescribedNeighborhood
import all Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.OriginalAffinePrescribedNeighborhood
public import Lean.Util.CollectAxioms
public import Batteries.Tactic.Lint
public import Mathlib.Tactic.Linter.TextBased

/-!
# Whole-boundary frames over the specified affine parameter

The original smooth-site base supplies separatedness, not an extra affineness
hypothesis. The given parameter remains unchanged throughout the construction.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open Scheme.Modules Scheme.Modules.Invertible

universe u

namespace MotivicTest.FixedParameterPrescribedFrame

/-- The actual specified frame extends in the unchanged fixed-parameter product,
including its whole possibly nonreduced boundary and its exact restriction. -/
theorem exists_original_fixedParameter_frame
    {k : Type u} [Field k] (S T : SmoothSite (Spec (.of k))) [IsAffine T.left]
    {A Z : Scheme.{u}} [IsAffine A] (a : A ⟶ S.left) (t : T.left ⟶ S.left)
    (z : Z ⟶ pullback t a) [IsClosedImmersion z] (L : LineBundle (pullback t a))
    (e : (Scheme.Modules.pullback z).obj L.val ≅ SheafOfModules.unit Z.ringCatSheaf) :
    ∃ (U : Scheme.{u}) (_ : IsAffine U) (v : U ⟶ pullback t a) (_ : IsOpenImmersion v)
      (b : Z ⟶ U) (hb : b ≫ v = z)
      (d : (Scheme.Modules.pullback v).obj L.val ≅ SheafOfModules.unit U.ringCatSheaf),
      ((Scheme.Modules.pullbackCongr hb).app L.val).symm ≪≫
        ((Scheme.Modules.pullbackComp b v).app L.val).symm ≪≫
        (Scheme.Modules.pullback b).mapIso d ≪≫ pullbackUnitIso b = e := by
  have : IsAffine (pullback t a) :=
    Scheme.RelativeCurve.isAffine_fixedParameter_boundaryNeighborhood
      (show S.left ⟶ Spec (.of k) from S.hom) a t
  have : IsAffine Z := isAffine_of_isAffineHom z
  exact exists_original_affine_open_prescribed_frame z L e

open Lean Batteries.Tactic.Lint in
run_cmd do
  let env ← getEnv
  let sourceModules := #[
    `Motivic.Aglib.AlgebraicGeometry.RelativeCurve.FixedParameterBoundaryNeighborhood,
    `Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.AffinePrescribedNeighborhood,
    `Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.OriginalAffinePrescribedNeighborhood]
  let modules := env.header.moduleNames.map (sourceModules.contains ·)
  let declarations := env.constants.map₁.fold
    (init := ← Lean.Elab.Command.liftCoreM getDeclsInCurrModule) fun declarations name _ =>
      if modules[env.const2ModIdx[name]?.get!]! then declarations.push name else declarations
  unless declarations.size ≥ 8 do
    throwError "Exact-origin original prescribed-frame declarations are missing."
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
    `Motivic.Aglib.AlgebraicGeometry.RelativeCurve.FixedParameterBoundaryNeighborhood,
    `Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.AffinePrescribedNeighborhood,
    `Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.OriginalAffinePrescribedNeighborhood,
    `MotivicTest.FixedParameterPrescribedFrame]
  let errors ← lintModules options #[] modules .humanReadable false
  let casingErrors ← modulesNotUpperCamelCase options modules
  let filenameErrors ← modulesOSForbidden options modules
  unless errors == 0 && casingErrors == 0 && filenameErrors == 0 do
    throwError "Exact-file source text/style checks failed."
  logInfo "Pinned text/style checks passed for all four selected modules."

end MotivicTest.FixedParameterPrescribedFrame
