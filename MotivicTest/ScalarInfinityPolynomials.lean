/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Bertini.QuadraticScalarInfinityPolynomials
public import Mathlib.RingTheory.Flat.Stability
import all Motivic.Aglib.RingTheory.MinimalPrimeGoingDown
import all Motivic.Aglib.RingTheory.Bertini.QuadraticBoundaryScalarMap
import all Motivic.Aglib.RingTheory.Bertini.QuadraticScalarInfinityAvoidance
import all Motivic.Aglib.RingTheory.Bertini.QuadraticScalarBoundaryAvoidance
import all Motivic.Aglib.RingTheory.Bertini.QuadraticScalarClosedInfinityAvoidance
import all Motivic.Aglib.RingTheory.Bertini.QuadraticScalarInfinityPolynomials
public import Lean.Util.CollectAxioms
public import Batteries.Tactic.Lint
public import Mathlib.Tactic.Linter.TextBased

/-! # Original polynomials on the actual scalar tensor and original extended ideal -/

@[expose] public noncomputable section

open MvPolynomial QuadraticIncidence.InfinityChart
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace MotivicTest.ScalarInfinityPolynomials

universe u

/-- The original polynomials precede the extension. Both conclusions refer to
the actual scalar tensor, including the whole original extended closed ideal. -/
theorem actual_tensor_infinity_avoidance
    (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R]
    [Algebra.FiniteType k R] (I : Ideal R) (hI : I ≠ ⊥)
    {σ : Type u} [Finite σ] (g : σ → R) (d : ℕ)
    (hd : Algebra.trdeg k R ≤ (d : Cardinal.{u}) + 1) :
    ∃ (F : MvPolynomial (Fin (d + 1) × QuadraticIncidence.Exponent σ) k)
      (Q : MvPolynomial (Fin d × QuadraticIncidence.Exponent σ) k),
      F ≠ 0 ∧ Q ≠ 0 ∧
      ∀ (L : Type u) [Field L] [Algebra k L] [IsDomain (R ⊗[k] L)]
        (z : Fin (d + 1) × QuadraticIncidence.Exponent σ → L)
        (c : Fin d × QuadraticIncidence.Exponent σ → L),
        eval₂ (algebraMap k L) z F ≠ 0 → eval₂ (algebraMap k L) c Q ≠ 0 →
        NoCommonInfinityZero L (R ⊗[k] L) (algebraMap R (R ⊗[k] L) ∘ g) d z ∧
        NoCommonClosedInfinityZero L (R ⊗[k] L)
          (I.map (algebraMap R (R ⊗[k] L))) (algebraMap R (R ⊗[k] L) ∘ g) d c := by
  obtain ⟨F, Q, hF, hQ, h⟩ := exists_scalar_infinity_polynomials k R I hI g d hd
  refine ⟨F, Q, hF, hQ, ?_⟩
  intro L _ _ _ z c hz hc
  exact h L (R ⊗[k] L)
    (Algebra.TensorProduct.includeLeft_injective (R := k) (S := k)
      (A := R) (B := L) (algebraMap k L).injective) z c hz hc

open Lean Batteries.Tactic.Lint in
run_cmd do
  let env ← getEnv
  let sourceModules := #[
    `Motivic.Aglib.RingTheory.MinimalPrimeGoingDown,
    `Motivic.Aglib.RingTheory.Bertini.QuadraticBoundaryScalarMap,
    `Motivic.Aglib.RingTheory.Bertini.QuadraticScalarInfinityAvoidance,
    `Motivic.Aglib.RingTheory.Bertini.QuadraticScalarBoundaryAvoidance,
    `Motivic.Aglib.RingTheory.Bertini.QuadraticScalarClosedInfinityAvoidance,
    `Motivic.Aglib.RingTheory.Bertini.QuadraticScalarInfinityPolynomials]
  let modules := env.header.moduleNames.map (sourceModules.contains ·)
  let declarations := env.constants.map₁.fold
    (init := ← Lean.Elab.Command.liftCoreM getDeclsInCurrModule) fun declarations name _ =>
      if modules[env.const2ModIdx[name]?.get!]! then declarations.push name else declarations
  unless declarations.size ≥ 15 do
    throwError "Exact-origin scalar infinity declarations are missing."
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
    `Motivic.Aglib.RingTheory.MinimalPrimeGoingDown,
    `Motivic.Aglib.RingTheory.Bertini.QuadraticBoundaryScalarMap,
    `Motivic.Aglib.RingTheory.Bertini.QuadraticScalarInfinityAvoidance,
    `Motivic.Aglib.RingTheory.Bertini.QuadraticScalarBoundaryAvoidance,
    `Motivic.Aglib.RingTheory.Bertini.QuadraticScalarClosedInfinityAvoidance,
    `Motivic.Aglib.RingTheory.Bertini.QuadraticScalarInfinityPolynomials,
    `MotivicTest.ScalarInfinityPolynomials]
  let errors ← lintModules options #[] modules .humanReadable false
  let casingErrors ← modulesNotUpperCamelCase options modules
  let filenameErrors ← modulesOSForbidden options modules
  unless errors == 0 && casingErrors == 0 && filenameErrors == 0 do
    throwError "Exact-file source text/style checks failed."
  logInfo "Pinned text/style checks passed for all seven selected modules."

end MotivicTest.ScalarInfinityPolynomials
