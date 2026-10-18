/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.FiniteAlgebraMarkedNorm
public import Motivic.Aglib.RingTheory.DVRNormCartierLength
import all Motivic.Aglib.RingTheory.FiniteAlgebraMarkedNorm
import all Motivic.Aglib.RingTheory.DVRNormCartierLength
public import Lean.Util.CollectAxioms
public import Batteries.Tactic.Lint
public import Mathlib.Tactic.Linter.TextBased

/-!
# Original covering norm consumers

The marked-fiber calculation uses the original character, without reducedness
of the other branches. The coefficient calculation starts from the genuine
generic field norm and recovers the original quotient length and all weighted
local lengths of the whole finite algebra. It does not assume individual source
stalks finite over the base DVR, or assert scheme-level divisor compatibility.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace MotivicTest.CoveringNormLengths

attribute [local instance] RingHom.ker_isPrime
  FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- A prescribed marked value is the specialization of the original norm,
even when the other fiber branches are nonreduced. -/
theorem original_norm_has_marked_value
    {R S k : Type*} [CommRing R] [CommRing S] [Field k]
    [Algebra R S] [Algebra R k] [Module.Free R S] [Module.Finite R S]
    (φ : (k ⊗[R] S) →ₐ[k] k) [Algebra.IsUnramifiedAt k (RingHom.ker φ)]
    (s : S) (a : k) (ha : φ ((1 : k) ⊗ₜ[R] s) = a)
    (hone : ∀ q : MaximalSpectrum (k ⊗[R] S), q.asIdeal ≠ RingHom.ker φ →
      Ideal.Quotient.mk q.asIdeal ((1 : k) ⊗ₜ[R] s) = 1) :
    algebraMap R k (Algebra.norm R s) = a :=
  (Algebra.map_norm_eq_fiber_character φ s hone).trans ha

/-- Any base element representing the actual generic field norm has both the
original Cartier quotient length and its full residue-weighted coefficient.
No separability or perfectness is used. -/
theorem original_lengths_of_generic_norm_value
    {R S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [Algebra R S]
    [Module.Finite R S] [Module.IsTorsionFree R S]
    (s : S) (hs : s ≠ 0) (n : R)
    (hn : algebraMap R (FractionRing R) n =
      Algebra.norm (FractionRing R) (algebraMap S (FractionRing S) s)) :
    Module.length R (S ⧸ Ideal.span {s}) = IsDiscreteValuationRing.addVal R n ∧
      IsDiscreteValuationRing.addVal R n =
        Module.finiteAlgebraFiberLengthSum
          (M := S ⧸ Ideal.span {s}) R S := by
  have he : n = Algebra.intNorm R S s := by
    apply IsFractionRing.injective R (FractionRing R)
    exact hn.trans (Algebra.algebraMap_intNorm_fractionRing s).symm
  rw [he]
  exact ⟨IsDiscreteValuationRing.length_quotient_span_eq_addVal_intNorm s hs,
    IsDiscreteValuationRing.addVal_intNorm_eq_fiberLengthSum s hs⟩

open Lean Batteries.Tactic.Lint in
run_cmd do
  let env ← getEnv
  let sourceModules := #[
    `Motivic.Aglib.RingTheory.FiniteAlgebraMarkedNorm,
    `Motivic.Aglib.RingTheory.DVRNormCartierLength]
  let modules := env.header.moduleNames.map (sourceModules.contains ·)
  let declarations := env.constants.map₁.fold
    (init := ← Lean.Elab.Command.liftCoreM getDeclsInCurrModule) fun declarations name _ =>
      if modules[env.const2ModIdx[name]?.get!]! then declarations.push name else declarations
  unless declarations.size ≥ 11 do
    throwError "Exact-origin original covering norm declarations are missing."
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
    `Motivic.Aglib.RingTheory.FiniteAlgebraMarkedNorm,
    `Motivic.Aglib.RingTheory.DVRNormCartierLength,
    `MotivicTest.CoveringNormLengths]
  let errors ← lintModules options #[] modules .humanReadable false
  let casingErrors ← modulesNotUpperCamelCase options modules
  let filenameErrors ← modulesOSForbidden options modules
  unless errors == 0 && casingErrors == 0 && filenameErrors == 0 do
    throwError "Exact-file source text/style checks failed."
  logInfo "Pinned text/style checks passed for all three selected modules."

end MotivicTest.CoveringNormLengths
