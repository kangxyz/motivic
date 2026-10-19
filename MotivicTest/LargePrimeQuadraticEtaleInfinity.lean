/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Bertini.LargePrimeQuadraticEtaleInfinity
import all Motivic.Aglib.RingTheory.Kaehler.ScalarResidueCotangent
import all Motivic.Aglib.RingTheory.Kaehler.ScalarResidueGradient
import all Motivic.Aglib.RingTheory.Kaehler.ScalarClosedPointCotangentBasis
import all Motivic.Aglib.RingTheory.Kaehler.ScalarClosedPointCotangentCoordinates
import all Motivic.Aglib.RingTheory.Kaehler.ScalarLinearCombinationDifferentialCoordinates
import all Motivic.Aglib.RingTheory.Bertini.ScalarQuadraticDifferentialMatrix
import all Motivic.Aglib.RingTheory.Bertini.ScalarQuadraticEtaleCriterion
import all Motivic.Aglib.RingTheory.Polynomial.Residue.FiberEvaluation
import all Motivic.Aglib.RingTheory.Bertini.ScalarQuadraticEtaleFromWholeFiber
import all Motivic.Aglib.RingTheory.Bertini.LargePrimeQuadraticEtaleInfinity
public import Lean.Util.CollectAxioms
public import Batteries.Tactic.Lint
public import Mathlib.Tactic.Linter.TextBased

/-! # Actual two-prime scalar étale and full infinity consumer audit -/

@[expose] public noncomputable section

open Module TensorProduct KaehlerDifferential _root_.MvPolynomial QuadraticIncidence
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace MotivicTest.LargePrimeQuadraticEtaleInfinity

universe u

/-- The actual producer retains the same chosen tuple in every conclusion. -/
theorem actual_same_tuple_etale_and_infinity
    (k R : Type u) [Field k] [Finite k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.Smooth k R]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (x : PrimeSpectrum R) [x.asIdeal.IsMaximal]
    (I : Ideal R) (hI : I ≠ ⊥)
    {σ : Type u} [Fintype σ] (g : σ → R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (hd : Algebra.trdeg k R ≤ (d : Cardinal.{u}) + 1)
    (B : Basis (Fin (d + 1)) x.asIdeal.ResidueField
      (x.asIdeal.ResidueField ⊗[R] Ω[R⁄k]))
    (f q : MvPolynomial (Fin d × Exponent σ) k)
    (hf : f ≠ 0) (hq : q ≠ 0) (N : ℕ) :
    ∃ n m : ℕ, N < n ∧ N < m ∧ n.Coprime m ∧
      ∀ (r : ℕ) [NeZero r], r = n ∨ r = m →
        let L := ULift.{u} (FiniteField.Extension k p r)
        Module.finrank k L = r ∧ ∃ hdom : IsDomain (R ⊗[k] L),
          letI : IsDomain (R ⊗[k] L) := hdom
          (∃! y : PrimeSpectrum (R ⊗[k] L),
            PrimeSpectrum.comap (algebraMap R (R ⊗[k] L)) y = x) ∧
          ∃ (a : Exponent σ → L) (c : Fin d × Exponent σ → L),
            eval₂ (algebraMap k L) c f ≠ 0 ∧ eval₂ (algebraMap k L) c q ≠ 0 ∧
            InfinityChart.NoCommonInfinityZero L (R ⊗[k] L)
              (algebraMap R (R ⊗[k] L) ∘ g) d (prependParameters L d a c) ∧
            InfinityChart.NoCommonClosedInfinityZero L (R ⊗[k] L)
              (I.map (algebraMap R (R ⊗[k] L)))
              (algebraMap R (R ⊗[k] L) ∘ g) d c ∧
            (let : Algebra (MvPolynomial (Fin d × Exponent σ) k) L :=
              (eval₂Hom (algebraMap k L) c).toAlgebra
             IsUnit (1 ⊗ₜ[MvPolynomial (Fin d × Exponent σ) k]
               (residueCoefficientEquiv k x.asIdeal.ResidueField _).symm
                 (selectedDeterminant d B
                   (selectedDerivative (k := k) (L := x.asIdeal.ResidueField) g)) :
               L ⊗[MvPolynomial (Fin d × Exponent σ) k]
                 (MvPolynomial (Fin d × Exponent σ) k ⊗[k] x.asIdeal.ResidueField))) ∧
            ∀ (y : PrimeSpectrum (R ⊗[k] L)),
              PrimeSpectrum.comap (algebraMap R (R ⊗[k] L)) y = x →
              ∃ s ∉ y.asIdeal,
                ((algebraMap (R ⊗[k] L) (Localization.Away s)).comp
                  (aeval (R := L) (fun i => aeval (algebraMap R (R ⊗[k] L) ∘ g)
                    (parameterTuple L σ (d + 1)
                      (prependParameters L d a c) i).val)).toRingHom).Etale :=
  exists_two_prime_quadratic_etale_infinity k R p x I hI g hg d hd B f q hf hq N

open Lean Batteries.Tactic.Lint in
run_cmd do
  let env ← getEnv
  let sourceModules := #[
    `Motivic.Aglib.RingTheory.Kaehler.ScalarResidueCotangent,
    `Motivic.Aglib.RingTheory.Kaehler.ScalarResidueGradient,
    `Motivic.Aglib.RingTheory.Kaehler.ScalarClosedPointCotangentBasis,
    `Motivic.Aglib.RingTheory.Kaehler.ScalarClosedPointCotangentCoordinates,
    `Motivic.Aglib.RingTheory.Kaehler.ScalarLinearCombinationDifferentialCoordinates,
    `Motivic.Aglib.RingTheory.Bertini.ScalarQuadraticDifferentialMatrix,
    `Motivic.Aglib.RingTheory.Bertini.ScalarQuadraticEtaleCriterion,
    `Motivic.Aglib.RingTheory.Polynomial.Residue.FiberEvaluation,
    `Motivic.Aglib.RingTheory.Bertini.ScalarQuadraticEtaleFromWholeFiber,
    `Motivic.Aglib.RingTheory.Bertini.LargePrimeQuadraticEtaleInfinity]
  let modules := env.header.moduleNames.map (sourceModules.contains ·)
  let declarations := env.constants.map₁.fold
    (init := ← Lean.Elab.Command.liftCoreM getDeclsInCurrModule) fun declarations name _ =>
      if modules[env.const2ModIdx[name]?.get!]! then declarations.push name else declarations
  unless declarations.size ≥ 15 do
    throwError "Exact-origin scalar cotangent and étale declarations are missing."
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
    `Motivic.Aglib.RingTheory.Kaehler.ScalarResidueCotangent,
    `Motivic.Aglib.RingTheory.Kaehler.ScalarResidueGradient,
    `Motivic.Aglib.RingTheory.Kaehler.ScalarClosedPointCotangentBasis,
    `Motivic.Aglib.RingTheory.Kaehler.ScalarClosedPointCotangentCoordinates,
    `Motivic.Aglib.RingTheory.Kaehler.ScalarLinearCombinationDifferentialCoordinates,
    `Motivic.Aglib.RingTheory.Bertini.ScalarQuadraticDifferentialMatrix,
    `Motivic.Aglib.RingTheory.Bertini.ScalarQuadraticEtaleCriterion,
    `Motivic.Aglib.RingTheory.Polynomial.Residue.FiberEvaluation,
    `Motivic.Aglib.RingTheory.Bertini.ScalarQuadraticEtaleFromWholeFiber,
    `Motivic.Aglib.RingTheory.Bertini.LargePrimeQuadraticEtaleInfinity,
    `MotivicTest.LargePrimeQuadraticEtaleInfinity]
  let errors ← lintModules options #[] modules .humanReadable false
  let casingErrors ← modulesNotUpperCamelCase options modules
  let filenameErrors ← modulesOSForbidden options modules
  unless errors == 0 && casingErrors == 0 && filenameErrors == 0 do
    throwError "Exact-file source text/style checks failed."
  logInfo "Pinned text/style checks passed for all eleven selected modules."

end MotivicTest.LargePrimeQuadraticEtaleInfinity
