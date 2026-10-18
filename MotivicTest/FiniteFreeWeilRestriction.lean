/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.AffineFiniteFreeWeilRestriction
import all Motivic.Aglib.RingTheory.FiniteFreeWeilRestriction
import all Motivic.Aglib.RingTheory.FiniteFreeWeilRestrictionHom
import all Motivic.Aglib.RingTheory.FiniteFreeWeilRestrictionPresentation
import all Motivic.Aglib.RingTheory.FiniteFreeWeilRestrictionEtale
import all Motivic.Aglib.RingTheory.FiniteFreeWeilRestrictionEtalePresentation
import all Motivic.Aglib.AlgebraicGeometry.AffineFiniteFreeWeilRestriction
public import Lean.Util.CollectAxioms
public import Batteries.Tactic.Lint
public import Mathlib.Tactic.Linter.TextBased

/-!
# Actual finite-free restriction algebra with a whole closed marking

The marking is the full quotient by an arbitrary ideal, not its reduction or
a chosen residue-field branch. No representing equivalence is supplied.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open Module Algebra.WeilRestriction

universe u

namespace MotivicTest.FiniteFreeWeilRestriction

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- An original étale algebra has an actual étale restriction algebra whose
literal evaluation uniquely lifts the entire possibly nonreduced closed mark. -/
theorem actual_etale_whole_closed_mark
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra.Etale B C]
    {κ : Type*} [Fintype κ] (b : Basis κ A B) (I : Ideal A)
    (g : C →ₐ[B] (A ⧸ I) ⊗[A] B) :
    Algebra.Etale A (Algebra.WeilRestriction.Ring b C) ∧
      ∃! h : Algebra.WeilRestriction.Ring b C →ₐ[A] A ⧸ I,
        ∀ c, Algebra.TensorProduct.map h (AlgHom.id A B)
          (evaluation b (Algebra.Presentation.ofFinitePresentation B C) c) = g c := by
  exact ⟨inferInstance,
    existsUnique_evaluation_lift b (Algebra.Presentation.ofFinitePresentation B C) g⟩

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/-- The corresponding genuine scalar-pullback scheme diagram preserves a whole closed quotient. -/
theorem actual_affine_whole_closed_mark
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra.Etale B C]
    {κ : Type u} [Fintype κ] (b : Basis κ A B) (I : Ideal A)
    (g : C →ₐ[B] (A ⧸ I) ⊗[A] B) :
    Etale (AffineWeilRestriction.projection (C := C) b) ∧
      AffineWeilRestriction.mark b g ≫ AffineWeilRestriction.projection b =
        Spec.algebraMap A (A ⧸ I) ∧
      AffineWeilRestriction.scalarMark b g ≫ AffineWeilRestriction.scalarEvaluation b =
        (pullbackSpecIso A (A ⧸ I) B).hom ≫ Spec.map (CommRingCat.ofHom g.toRingHom) := by
  exact ⟨inferInstance, AffineWeilRestriction.mark_over b g,
    AffineWeilRestriction.scalarMark_evaluation b g⟩

open Lean Batteries.Tactic.Lint in
run_cmd do
  let env ← getEnv
  let sourceModules := #[
    `Motivic.Aglib.RingTheory.FiniteFreeWeilRestriction,
    `Motivic.Aglib.RingTheory.FiniteFreeWeilRestrictionHom,
    `Motivic.Aglib.RingTheory.FiniteFreeWeilRestrictionPresentation,
    `Motivic.Aglib.RingTheory.FiniteFreeWeilRestrictionEtale,
    `Motivic.Aglib.RingTheory.FiniteFreeWeilRestrictionEtalePresentation,
    `Motivic.Aglib.AlgebraicGeometry.AffineFiniteFreeWeilRestriction]
  let modules := env.header.moduleNames.map (sourceModules.contains ·)
  let declarations := env.constants.map₁.fold
    (init := ← Lean.Elab.Command.liftCoreM getDeclsInCurrModule) fun declarations name _ =>
      if modules[env.const2ModIdx[name]?.get!]! then declarations.push name else declarations
  unless declarations.size ≥ 35 do
    throwError "Exact-origin finite-free restriction declarations are missing."
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
    `Motivic.Aglib.RingTheory.FiniteFreeWeilRestriction,
    `Motivic.Aglib.RingTheory.FiniteFreeWeilRestrictionHom,
    `Motivic.Aglib.RingTheory.FiniteFreeWeilRestrictionPresentation,
    `Motivic.Aglib.RingTheory.FiniteFreeWeilRestrictionEtale,
    `Motivic.Aglib.RingTheory.FiniteFreeWeilRestrictionEtalePresentation,
    `Motivic.Aglib.AlgebraicGeometry.AffineFiniteFreeWeilRestriction,
    `MotivicTest.FiniteFreeWeilRestriction]
  let errors ← lintModules options #[] modules .humanReadable false
  let casingErrors ← modulesNotUpperCamelCase options modules
  let filenameErrors ← modulesOSForbidden options modules
  unless errors == 0 && casingErrors == 0 && filenameErrors == 0 do
    throwError "Exact-file source text/style checks failed."
  logInfo "Pinned text/style checks passed for all seven selected modules."

end MotivicTest.FiniteFreeWeilRestriction
