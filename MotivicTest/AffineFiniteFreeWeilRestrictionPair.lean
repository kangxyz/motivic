/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.AffineFiniteFreeWeilRestrictionPair
import all Motivic.Aglib.AlgebraicGeometry.AffineFiniteFreeWeilRestrictionPair
public import Lean.Util.CollectAxioms
public import Batteries.Tactic.Lint
public import Mathlib.Tactic.Linter.TextBased

/-!
# Two actual affine scalar witnesses on one original marked refinement

Both evaluations use the scalar extensions of the same original product and
its same whole closed quotient marking. The ideal need not be radical.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Module AffineWeilRestriction
open scoped TensorProduct

universe u

namespace MotivicTest.AffineFiniteFreeWeilRestrictionPair

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Two actual scalar étale witnesses admit one common original affine étale
refinement retaining the entire closed marking and both scalar evaluations. -/
theorem actual_common_original_closed_refinement
    {A B₁ B₂ C₁ C₂ : Type u}
    [CommRing A] [CommRing B₁] [CommRing B₂] [CommRing C₁] [CommRing C₂]
    [Algebra A B₁] [Algebra A B₂] [Algebra B₁ C₁] [Algebra B₂ C₂]
    [Algebra.Etale B₁ C₁] [Algebra.Etale B₂ C₂]
    {κ₁ κ₂ : Type u} [Fintype κ₁] [Fintype κ₂]
    (b₁ : Basis κ₁ A B₁) (b₂ : Basis κ₂ A B₂) (I : Ideal A)
    (g₁ : C₁ →ₐ[B₁] (A ⧸ I) ⊗[A] B₁) (g₂ : C₂ →ₐ[B₂] (A ⧸ I) ⊗[A] B₂) :
    IsAffine (pairScheme (C₁ := C₁) (C₂ := C₂) b₁ b₂) ∧
      Etale (pairProjection (C₁ := C₁) (C₂ := C₂) b₁ b₂) ∧
      pairMark b₁ b₂ g₁ g₂ ≫ pairProjection b₁ b₂ = Spec.algebraMap A (A ⧸ I) ∧
      pairScalarMark b₁ b₂ g₁ g₂ B₁ ≫ pairEvaluationLeft b₁ b₂ =
        (pullbackSpecIso A (A ⧸ I) B₁).hom ≫ Spec.map (CommRingCat.ofHom g₁.toRingHom) ∧
      pairScalarMark b₁ b₂ g₁ g₂ B₂ ≫ pairEvaluationRight b₁ b₂ =
        (pullbackSpecIso A (A ⧸ I) B₂).hom ≫ Spec.map (CommRingCat.ofHom g₂.toRingHom) := by
  exact ⟨inferInstance, inferInstance, pairMark_over b₁ b₂ g₁ g₂,
    pairEvaluationLeft_mark b₁ b₂ g₁ g₂, pairEvaluationRight_mark b₁ b₂ g₁ g₂⟩

open Lean Batteries.Tactic.Lint in
run_cmd do
  let env ← getEnv
  let sourceModules := #[
    `Motivic.Aglib.AlgebraicGeometry.AffineFiniteFreeWeilRestrictionPair]
  let modules := env.header.moduleNames.map (sourceModules.contains ·)
  let declarations := env.constants.map₁.fold
    (init := ← Lean.Elab.Command.liftCoreM getDeclsInCurrModule) fun declarations name _ =>
      if modules[env.const2ModIdx[name]?.get!]! then declarations.push name else declarations
  unless declarations.size ≥ 18 do
    throwError "Exact-origin common affine restriction declarations are missing."
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
    `Motivic.Aglib.AlgebraicGeometry.AffineFiniteFreeWeilRestrictionPair,
    `MotivicTest.AffineFiniteFreeWeilRestrictionPair]
  let errors ← lintModules options #[] modules .humanReadable false
  let casingErrors ← modulesNotUpperCamelCase options modules
  let filenameErrors ← modulesOSForbidden options modules
  unless errors == 0 && casingErrors == 0 && filenameErrors == 0 do
    throwError "Exact-file source text/style checks failed."
  logInfo "Pinned text/style checks passed for both selected modules."

end MotivicTest.AffineFiniteFreeWeilRestrictionPair
