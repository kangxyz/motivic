/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.ContractionBoundarySheafComparison
public import Motivic.Cohomology.A1.ContractionBoundaryMono
import all Motivic.Cohomology.A1.PresheafBoundarySheafComparison
import all Motivic.Cohomology.A1.ContractionBoundarySheafComparison
import Lean.Util.CollectAxioms
import Batteries.Tactic.Lint

/-! # A conditional canonical-boundary isomorphism through the explicit sheaf comparisons -/

set_option linter.hashCommand false

public noncomputable section

open CategoryTheory AlgebraicGeometry Motivic

universe u

namespace MotivicTest.ContractionBoundarySheafComparison

variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))
  (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant)

/-- An explicitly supplied original-presheaf Epi transfers to the old canonical
sheaf map through the proved square. The Epi input is not discharged here. -/
theorem original_canonical_epi
    (hE : Epi (FiniteEtaleSite.OriginalPresheaf.contractionToBoundary X F.obj)) :
    Epi (FiniteEtaleSite.contractionToBoundary X F hF) := by
  let := hE
  let : Epi ((FiniteEtaleSite.OriginalPresheaf.contractionSheafIso X F hF).hom ≫
      FiniteEtaleSite.contractionToBoundary X F hF) := by
    rw [← FiniteEtaleSite.OriginalPresheaf.contractionToBoundary_sheafIso]
    infer_instance
  exact epi_of_epi (FiniteEtaleSite.OriginalPresheaf.contractionSheafIso X F hF).hom _

/-- Accepted canonical Mono and the explicit Epi input give an isomorphism of the
unchanged sheaf map. This remains a conditional consumer, not unconditional purity. -/
theorem original_canonical_iso
    (hE : Epi (FiniteEtaleSite.OriginalPresheaf.contractionToBoundary X F.obj)) :
    IsIso (FiniteEtaleSite.contractionToBoundary X F hF) := by
  let := original_canonical_epi X F hF hE
  let := FiniteEtaleSite.contractionToBoundary_mono X F hF
  exact isIso_of_mono_of_epi _

open Lean in
run_cmd do
  for dependency in ← collectAxioms ``original_canonical_iso do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
      throwError "The conditional canonical-boundary consumer depends on {dependency}"
  logInfo "Conditional canonical-boundary isomorphism: explicit Epi input, standard axioms only."

open Lean Batteries.Tactic.Lint in
run_cmd do
  let env ← getEnv
  let sourceModules := #[`Motivic.Cohomology.A1.PresheafBoundarySheafComparison,
    `Motivic.Cohomology.A1.ContractionBoundarySheafComparison]
  let modules := env.header.moduleNames.map (sourceModules.contains ·)
  let declarations := env.constants.map₁.fold
    (init := ← Lean.Elab.Command.liftCoreM getDeclsInCurrModule) fun declarations name _ =>
      if modules[env.const2ModIdx[name]?.get!]! then declarations.push name else declarations
  unless declarations.size ≥ 11 do
    throwError "The original boundary comparison declarations are missing from this lint."
  let linters ← Lean.Elab.Command.liftCoreM (getChecks true none none)
  unless !linters.isEmpty do
    throwError "No declaration linters were selected."
  let results ← Lean.Elab.Command.liftCoreM <|
    Lean.withExporting (isExporting := false) (lintCore declarations linters)
  for (linter, findings) in results do
    for (name, message) in findings.toArray do
      throwError "{linter.name}: {name}: {message}"
  logInfo m!"Canonical boundary comparisons: {declarations.size} declarations passed lint."

end MotivicTest.ContractionBoundarySheafComparison
