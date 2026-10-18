/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.LargePrimeOriginalEtalePresentation
import all Motivic.Aglib.RingTheory.Bertini.SelectedMinorFieldExtension
import all Motivic.Aglib.RingTheory.Bertini.ScalarWholeFiberParameterIndependence
import all Motivic.Aglib.RingTheory.Bertini.ScalarMovingCoefficientMap
import all Motivic.Aglib.RingTheory.Bertini.ScalarWholeFiberDifferentialIndependence
import all Motivic.Aglib.RingTheory.FiniteScalarExtensionTrdeg
import all Motivic.Aglib.RingTheory.Bertini.ScalarWholeFiberSmoothProjection
import all Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.ChosenQuadraticCompactification
import all Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.LargePrimeQuadraticCompactification
import all Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.ChosenRetainedPresentation
import all Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.ChosenOriginalEtalePresentation
import all Motivic.Aglib.AlgebraicGeometry.AffineEtaleScalarClosedSquare
import all Motivic.AlgebraicGeometry.SmoothSiteAffineScalarCoordinates
import all Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.LargePrimeOriginalEtalePresentation
public import Lean.Util.CollectAxioms
public import Batteries.Tactic.Lint
public import Mathlib.Tactic.Linter.TextBased

/-! # Actual two-prime scalar original étale presentation consumer

Generators, positive transcendence degree, and the original residue cotangent
basis are explicit algebraic inputs. The original étale diagram is an input;
its scalar presentation, whole closed fiber, and integral scalar algebra are
produced, not assumed. This is not boundary Epi or finite-field strict invariance.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module MvPolynomial
open AlgebraicGeometry.Scheme.RelativeCurve QuadraticIncidence.InfinityChart
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace MotivicTest.LargePrimeOriginalEtalePresentation

universe u

/-- Actual same-degree scalar presentations preserve the literal original diagram. -/
theorem actual_two_prime_original_presentations
    (k B : Type u) [Field k] [Finite k] [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.Smooth k B]
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
    (x : PrimeSpectrum B) [x.asIdeal.IsMaximal]
    (J : Ideal B) (hJ : J ≠ ⊥)
    {σ : Type u} [Finite σ] (g : σ → B)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (hd : Algebra.trdeg k B = (d + 1 : ℕ))
    (basis : Basis (Fin (d + 1)) x.asIdeal.ResidueField
      (x.asIdeal.ResidueField ⊗[B] KaehlerDifferential k B))
    {Y A : Scheme.{u}} (p : Y ⟶ Spec (.of B)) [Etale p] [QuasiCompact p] [IsSeparated p]
    (a : A ⟶ Spec (.of B)) [IsOpenImmersion a]
    (s : Spec (.of (B ⧸ J)) ⟶ Y)
    (hs : s ≫ p = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
    (H : IsPullback s (𝟙 _) p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
    (ha : Disjoint (Set.range a)
      (Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))))
    (hcover : ∀ y : Spec (.of B), y ∈ Set.range a ∨
      y ∈ Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
    (N₀ : ℕ) :
    ∃ n m : ℕ, N₀ < n ∧ N₀ < m ∧ n.Coprime m ∧
      ∀ (r : ℕ) [NeZero r], r = n ∨ r = m →
        let L := ULift.{u} (FiniteField.Extension k ℓ r)
        let S := B ⊗[k] L
        let ρ := Spec.map (CommRingCat.ofHom (algebraMap B S))
        Module.finrank k L = r ∧ ∃ hdom : IsDomain S,
          letI : IsDomain S := hdom
          ∃ y : PrimeSpectrum S,
            PrimeSpectrum.comap (algebraMap B S) y = x ∧
            (∀ z : PrimeSpectrum S, PrimeSpectrum.comap (algebraMap B S) z = x → z = y) ∧
            Nonempty (OriginalEtalePresentation L
              (Spec.map (CommRingCat.ofHom (algebraMap L S)))
              (pullback.snd p ρ) (pullback.snd a ρ)
              (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J.map (algebraMap B S)))))
              (Scheme.quotientBaseChangeEtaleLift B S J p s hs) y) :=
  exists_two_prime_originalEtalePresentations k B ℓ x J hJ g hg d hd basis
    p a s hs H ha hcover N₀

open Lean Batteries.Tactic.Lint in
run_cmd do
  let env ← getEnv
  let sourceModules := #[
    `Motivic.Aglib.RingTheory.Bertini.SelectedMinorFieldExtension,
    `Motivic.Aglib.RingTheory.Bertini.ScalarWholeFiberParameterIndependence,
    `Motivic.Aglib.RingTheory.Bertini.ScalarMovingCoefficientMap,
    `Motivic.Aglib.RingTheory.Bertini.ScalarWholeFiberDifferentialIndependence,
    `Motivic.Aglib.RingTheory.FiniteScalarExtensionTrdeg,
    `Motivic.Aglib.RingTheory.Bertini.ScalarWholeFiberSmoothProjection,
    `Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.ChosenQuadraticCompactification,
    `Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.LargePrimeQuadraticCompactification,
    `Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.ChosenRetainedPresentation,
    `Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.ChosenOriginalEtalePresentation,
    `Motivic.Aglib.AlgebraicGeometry.AffineEtaleScalarClosedSquare,
    `Motivic.AlgebraicGeometry.SmoothSiteAffineScalarCoordinates,
    `Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.LargePrimeOriginalEtalePresentation]
  let modules := env.header.moduleNames.map (sourceModules.contains ·)
  let declarations := env.constants.map₁.fold
    (init := ← Lean.Elab.Command.liftCoreM getDeclsInCurrModule) fun declarations name _ =>
      if modules[env.const2ModIdx[name]?.get!]! then declarations.push name else declarations
  unless declarations.size ≥ 20 do
    throwError "Exact-origin scalar whole-fiber and original presentation declarations are missing."
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
    `Motivic.Aglib.RingTheory.Bertini.SelectedMinorFieldExtension,
    `Motivic.Aglib.RingTheory.Bertini.ScalarWholeFiberParameterIndependence,
    `Motivic.Aglib.RingTheory.Bertini.ScalarMovingCoefficientMap,
    `Motivic.Aglib.RingTheory.Bertini.ScalarWholeFiberDifferentialIndependence,
    `Motivic.Aglib.RingTheory.FiniteScalarExtensionTrdeg,
    `Motivic.Aglib.RingTheory.Bertini.ScalarWholeFiberSmoothProjection,
    `Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.ChosenQuadraticCompactification,
    `Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.LargePrimeQuadraticCompactification,
    `Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.ChosenRetainedPresentation,
    `Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.ChosenOriginalEtalePresentation,
    `Motivic.Aglib.AlgebraicGeometry.AffineEtaleScalarClosedSquare,
    `Motivic.AlgebraicGeometry.SmoothSiteAffineScalarCoordinates,
    `Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.LargePrimeOriginalEtalePresentation,
    `MotivicTest.LargePrimeOriginalEtalePresentation]
  let errors ← lintModules options #[] modules .humanReadable false
  let casingErrors ← modulesNotUpperCamelCase options modules
  let filenameErrors ← modulesOSForbidden options modules
  unless errors == 0 && casingErrors == 0 && filenameErrors == 0 do
    throwError "Exact-file source text/style checks failed."
  logInfo "Pinned text/style checks passed for all fourteen selected modules."


end MotivicTest.LargePrimeOriginalEtalePresentation
