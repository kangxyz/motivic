/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.Boundary.Contraction.Mono
import all Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.SectionDetection
import all Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.Complement
import all Motivic.Cohomology.A1.Boundary.Contraction.MarkedExtension
import all Motivic.Cohomology.A1.Contraction.LocalCylinderExtension
import all Motivic.Cohomology.A1.Boundary.Contraction.LocalKernel
import all Motivic.Cohomology.A1.Boundary.Contraction.Mono
import Lean.Util.CollectAxioms
import Batteries.Tactic.Lint

/-! # The unchanged canonical contraction boundary is a monomorphism -/

set_option linter.hashCommand false
public noncomputable section
open CategoryTheory AlgebraicGeometry Motivic Opposite
universe u
namespace MotivicTest.ContractionBoundaryMono
open _root_.AlgebraicGeometry.Scheme (EtaleSeparatedFiniteType SmoothSite)

variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))
  (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant)

/-- The original canonical morphism is monic without additional field hypotheses. -/
theorem original_canonical_mono : Mono (FiniteEtaleSite.contractionToBoundary X F hF) :=
  FiniteEtaleSite.contractionToBoundary_mono X F hF

/-- The kernel vanishes on the original small test object and contraction section. -/
theorem original_section_eq_zero (V : EtaleSeparatedFiniteType X.left)
    (c : (((_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.toSmoothSite X).op ⋙
        (PresheafWithTransfers.toPresheaf k).obj
      (PresheafWithTransfers.contraction F.obj)).obj (op V)))
    (hc : (FiniteEtaleSite.contractionToBoundary X F hF).hom.app (op V) c = 0) : c = 0 :=
  FiniteEtaleSite.contractionToBoundary_eq_zero X F hF V c hc

open Lean in
run_cmd do
  for name in #[``FiniteEtaleSite.contractionToBoundary_mono] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "The original canonical contraction boundary is monic: standard foundations only."

open Lean Batteries.Tactic.Lint in
run_cmd do
  let env ← getEnv
  let sourceModules := #[`Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.SectionDetection,
    `Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.Complement,
    `Motivic.Cohomology.A1.Boundary.Contraction.MarkedExtension,
    `Motivic.Cohomology.A1.Contraction.LocalCylinderExtension,
    `Motivic.Cohomology.A1.Boundary.Contraction.LocalKernel,
    `Motivic.Cohomology.A1.Boundary.Contraction.Mono]
  let modules := env.header.moduleNames.map (sourceModules.contains ·)
  let declarations := env.constants.map₁.fold
    (init := ← Lean.Elab.Command.liftCoreM getDeclsInCurrModule) fun declarations name _ =>
      if modules[env.const2ModIdx[name]?.get!]! then declarations.push name else declarations
  unless declarations.size ≥ 14 do
    throwError "The original contraction boundary source declarations are missing from this lint."
  let linters ← Lean.Elab.Command.liftCoreM (getChecks true none none)
  unless !linters.isEmpty do
    throwError "No declaration linters were selected."
  let results ← Lean.Elab.Command.liftCoreM <|
    Lean.withExporting (isExporting := false) (lintCore declarations linters)
  for (linter, findings) in results do
    for (name, message) in findings.toArray do
      throwError "{linter.name}: {name}: {message}"
  logInfo m!"Canonical contraction boundary: {declarations.size} declarations passed lint."

end MotivicTest.ContractionBoundaryMono
