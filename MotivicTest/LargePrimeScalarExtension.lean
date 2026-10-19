/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.FieldTheory.FiniteExtension.CoprimeTensorField
public import Motivic.Aglib.FieldTheory.FiniteExtension.PrimeDegrees
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.FiniteEtaleIntegralOfSingletonFiber
public import Motivic.Aglib.RingTheory.TensorProduct.ScalarExtension.CoprimeIntegral
public import Motivic.Aglib.RingTheory.TensorProduct.ScalarExtension.LargePrime
import all Motivic.Aglib.FieldTheory.FiniteExtension.CoprimeTensorField
import all Motivic.Aglib.FieldTheory.FiniteExtension.PrimeDegrees
import all Motivic.Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.FiniteEtaleIntegralOfSingletonFiber
import all Motivic.Aglib.RingTheory.TensorProduct.ScalarExtension.CoprimeIntegral
import all Motivic.Aglib.RingTheory.TensorProduct.ScalarExtension.LargePrime
public import Lean.Util.CollectAxioms
public import Batteries.Tactic.Lint
public import Mathlib.Tactic.Linter.TextBased

/-! # Actual large scalar extensions, integral schemes, full fibers and parameters -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

universe u v

namespace MotivicTest.LargePrimeScalarExtension

/-- Two actual scalar-extended integral affine schemes retain the entire
original closed mark, while the original parameter condition remains nonzero
in every further field. This does not invoke an infinite-field presentation. -/
theorem original_affine_schemes_full_fibers_and_parameters
    (k R : Type u) [Field k] [Finite k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.Smooth k R]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (x : PrimeSpectrum R) [x.asIdeal.IsMaximal]
    {σ : Type u} [Finite σ] (q : MvPolynomial σ k) (hq : q ≠ 0) (N : ℕ) :
    ∃ n m : ℕ, N < n ∧ N < m ∧ n.Coprime m ∧
      ∀ (r : ℕ) [NeZero r], r = n ∨ r = m →
        let L := ULift.{u} (FiniteField.Extension k p r)
        Module.finrank k L = r ∧ IsIntegral (Spec (.of (R ⊗[k] L))) ∧
          (∃! y : Spec (.of (R ⊗[k] L)),
            (Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[k] L)))) y = x) ∧
          ∃ c : σ → L, ∀ (E : Type v) [Field E] (φ : L →+* E),
            φ (MvPolynomial.eval₂ (algebraMap k L) c q) ≠ 0 := by
  obtain ⟨n, m, _, _, hNn, hNm, _, hnm, h⟩ :=
    Algebra.TensorProduct.exists_two_large_prime_scalar_extensions k R p x q hq N
  refine ⟨n, m, hNn, hNm, hnm, ?_⟩
  intro r _ hr
  obtain ⟨hdegree, hD, hunique, c, hc⟩ := h r hr
  let := hD
  refine ⟨hdegree, inferInstance, hunique, c, ?_⟩
  intro E _ φ
  exact fun hz => hc (φ.injective (by simpa using hz))

open Lean Batteries.Tactic.Lint in
run_cmd do
  let env ← getEnv
  let sourceModules := #[
    `Motivic.Aglib.FieldTheory.FiniteExtension.CoprimeTensorField,
    `Motivic.Aglib.FieldTheory.FiniteExtension.PrimeDegrees,
    `Motivic.Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.FiniteEtaleIntegralOfSingletonFiber,
    `Motivic.Aglib.RingTheory.TensorProduct.ScalarExtension.CoprimeIntegral,
    `Motivic.Aglib.RingTheory.TensorProduct.ScalarExtension.LargePrime]
  let modules := env.header.moduleNames.map (sourceModules.contains ·)
  let declarations := env.constants.map₁.fold
    (init := ← Lean.Elab.Command.liftCoreM getDeclsInCurrModule) fun declarations name _ =>
      if modules[env.const2ModIdx[name]?.get!]! then declarations.push name else declarations
  unless declarations.size ≥ 10 do
    throwError "Exact-origin large scalar extension declarations are missing."
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
    `Motivic.Aglib.FieldTheory.FiniteExtension.CoprimeTensorField,
    `Motivic.Aglib.FieldTheory.FiniteExtension.PrimeDegrees,
    `Motivic.Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.FiniteEtaleIntegralOfSingletonFiber,
    `Motivic.Aglib.RingTheory.TensorProduct.ScalarExtension.CoprimeIntegral,
    `Motivic.Aglib.RingTheory.TensorProduct.ScalarExtension.LargePrime,
    `MotivicTest.LargePrimeScalarExtension]
  let errors ← lintModules options #[] modules .humanReadable false
  let casingErrors ← modulesNotUpperCamelCase options modules
  let filenameErrors ← modulesOSForbidden options modules
  unless errors == 0 && casingErrors == 0 && filenameErrors == 0 do
    throwError "Exact-file source text/style checks failed."
  logInfo "Pinned text/style checks passed for all six selected modules."

end MotivicTest.LargePrimeScalarExtension
