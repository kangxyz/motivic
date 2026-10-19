/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.FieldTheory.FiniteExtension.Avoidance.Polynomial
public import Motivic.Aglib.FieldTheory.FiniteExtension.Avoidance.WholeFiber
public import Motivic.Aglib.FieldTheory.FiniteExtension.Avoidance.ResiduePolynomial
public import Motivic.Aglib.RingTheory.Bertini.FiniteExtensionMovingPointParameters
import all Motivic.Aglib.FieldTheory.FiniteExtension.Avoidance.Polynomial
import all Motivic.Aglib.FieldTheory.FiniteExtension.Avoidance.WholeFiber
import all Motivic.Aglib.FieldTheory.FiniteExtension.Avoidance.ResiduePolynomial
import all Motivic.Aglib.RingTheory.Bertini.FiniteExtensionMovingPointParameters
public import Lean.Util.CollectAxioms
public import Batteries.Tactic.Lint
public import Mathlib.Tactic.Linter.TextBased

/-!
# All-branch finite-extension parameter consumers

The first consumer detects the actual residue polynomial on every field-valued
branch of every original finite-family tensor fiber. The second preserves the
literal original moving-point chart equations and their extension evaluations.
Neither consumer asserts construction of an original étale presentation.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct
open _root_.MvPolynomial

universe u v w z

namespace MotivicTest.FiniteExtensionParameterAvoidance

/-- One finite-extension parameter works on every field-valued branch of each
member of the finite residue family, not just one selected tensor component. -/
theorem original_residue_polynomials_nonzero_on_every_branch
    (k : Type u) [Field k] [Finite k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {ι : Type v} [Finite ι] (K : ι → Type v)
    [∀ i, Field (K i)] [∀ i, Algebra k (K i)] [∀ i, Module.Finite k (K i)]
    {σ : Type w} [Finite σ]
    (q : (i : ι) → MvPolynomial σ (K i)) (hq : ∀ i, q i ≠ 0) :
    ∃ N : ℕ, ∀ (n : ℕ) [NeZero n], N < n →
      ∃ c : σ → FiniteField.Extension k p n,
        let : Algebra (MvPolynomial σ k) (FiniteField.Extension k p n) :=
          (eval₂Hom (algebraMap k (FiniteField.Extension k p n)) c).toAlgebra
        ∀ (i : ι) (E : Type z) [Field E]
          (φ : (FiniteField.Extension k p n ⊗[MvPolynomial σ k]
            (MvPolynomial σ k ⊗[k] K i)) →+* E),
          φ (1 ⊗ₜ[MvPolynomial σ k]
            (residueCoefficientEquiv k (K i) σ).symm (q i)) ≠ 0 := by
  obtain ⟨N, hN⟩ := exists_isUnit_simultaneous_residuePolynomials_finiteExtension k p K q hq
  refine ⟨N, ?_⟩
  intro n _ hn
  obtain ⟨c, hc⟩ := hN n hn
  refine ⟨c, ?_⟩
  dsimp only at hc ⊢
  intro i E _ φ
  exact ((hc i).map φ).ne_zero

/-- Original bad-chart relations remain zero, while their parameter value is
nonzero in every further field receiving the selected finite extension. -/
theorem original_chart_relations_and_extension_values
    (k R B : Type u) [Field k] [Finite k] [CommRing R] [IsDomain R] [CommRing B]
    [Algebra k R] [Algebra k B] [Algebra R B] [IsScalarTower k R B]
    [Module.Finite R B] [Algebra.Smooth k R]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    {σ : Type u} [Fintype σ]
    (g : σ → R) (hg : Algebra.adjoin k (Set.range g) = ⊤)
    (a : σ → B) (d : ℕ) (hd : Algebra.trdeg k R = (d + 1 : ℕ))
    (q : MvPolynomial (Fin d × QuadraticIncidence.Exponent σ) k) (hq : q ≠ 0) :
    ∃ (f : MvPolynomial (Fin d × QuadraticIncidence.Exponent σ) k) (N : ℕ),
      (∀ (i₀ : Fin d) (j : σ),
        QuadraticIncidence.MovingPointChart.chartParameterMap k R B g a d i₀ j f = 0) ∧
      ∀ (n : ℕ) [NeZero n], N < n →
        ∃ c : Fin d × QuadraticIncidence.Exponent σ → FiniteField.Extension k p n,
          eval₂ (algebraMap k (FiniteField.Extension k p n)) c q ≠ 0 ∧
          ∀ (E : Type z) [Field E] (φ : FiniteField.Extension k p n →+* E),
            φ (eval₂ (algebraMap k (FiniteField.Extension k p n)) c f) ≠ 0 := by
  obtain ⟨f, N, _, hz, hN⟩ :=
    QuadraticIncidence.MovingPointChart.exists_parameter_choice_avoiding_charts_finiteExtension
      k R B p g hg a d hd q hq
  refine ⟨f, N, hz, ?_⟩
  intro n _ hn
  obtain ⟨c, hf, hc⟩ := hN n hn
  refine ⟨c, hc, ?_⟩
  intro E _ φ
  exact fun h => hf (φ.injective (by simpa using h))

open Lean Batteries.Tactic.Lint in
run_cmd do
  let env ← getEnv
  let sourceModules := #[
    `Motivic.Aglib.FieldTheory.FiniteExtension.Avoidance.Polynomial,
    `Motivic.Aglib.FieldTheory.FiniteExtension.Avoidance.WholeFiber,
    `Motivic.Aglib.FieldTheory.FiniteExtension.Avoidance.ResiduePolynomial,
    `Motivic.Aglib.RingTheory.Bertini.FiniteExtensionMovingPointParameters]
  let modules := env.header.moduleNames.map (sourceModules.contains ·)
  let declarations := env.constants.map₁.fold
    (init := ← Lean.Elab.Command.liftCoreM getDeclsInCurrModule) fun declarations name _ =>
      if modules[env.const2ModIdx[name]?.get!]! then declarations.push name else declarations
  unless declarations.size ≥ 11 do
    throwError "Exact-origin finite-extension parameter declarations are missing."
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
    `Motivic.Aglib.FieldTheory.FiniteExtension.Avoidance.Polynomial,
    `Motivic.Aglib.FieldTheory.FiniteExtension.Avoidance.WholeFiber,
    `Motivic.Aglib.FieldTheory.FiniteExtension.Avoidance.ResiduePolynomial,
    `Motivic.Aglib.RingTheory.Bertini.FiniteExtensionMovingPointParameters,
    `MotivicTest.FiniteExtensionParameterAvoidance]
  let errors ← lintModules options #[] modules .humanReadable false
  let casingErrors ← modulesNotUpperCamelCase options modules
  let filenameErrors ← modulesOSForbidden options modules
  unless errors == 0 && casingErrors == 0 && filenameErrors == 0 do
    throwError "Exact-file source text/style checks failed."
  logInfo "Pinned text/style checks passed for all five selected modules."

end MotivicTest.FiniteExtensionParameterAvoidance
