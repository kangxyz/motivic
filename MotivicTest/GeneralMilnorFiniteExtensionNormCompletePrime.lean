/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.KTheory.MilnorK.FiniteExtensionNormCompletePrime
import Motivic.KTheory.MilnorK.FiniteExtensionNormDVRResidueTower
import Lean.Util.CollectAxioms

/-! Actual complete-DVR prime square, no residue compatibility hypotheses. -/

namespace MotivicTest.GeneralMilnorFiniteExtensionNormCompletePrime

open Motivic.KTheory.MilnorK IsLocalRing

universe u

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R] [CharZero (ResidueField R)]
  (F : Type u) [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]

/-- Every actual finite normal-prime extension satisfies the local square in
any specified finite DVR integral closure of the original complete base. -/
theorem actual_complete_prime_square
    (E : Type u) [Field E] [Algebra F E] [FiniteDimensional F E] [Normal F E]
    [Algebra R E] [IsScalarTower R F E]
    (S : Type*) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra R S] [Module.Finite R S] [IsLocalHom (algebraMap R S)]
    [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
    [IsIntegralClosure S R E]
    (hp : (Module.finrank F E).Prime) (n : ℕ) (x : K E (n + 1)) :
    DVR.residue R F n (finiteExtensionNorm F E (n + 1) x) =
      finiteExtensionNorm (ResidueField R) (ResidueField S) n (DVR.residue S E n x) :=
  residue_finiteExtensionNorm_complete_prime R F E S hp n x

end MotivicTest.GeneralMilnorFiniteExtensionNormCompletePrime

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`AdjoinRoot, `Motivic.KTheory.MilnorK,
    `MotivicTest.GeneralMilnorFiniteExtensionNormCompletePrime]
  let selected (name : Name) := prefixes.any (·.isPrefixOf name)
  let mut names : NameSet := {}
  for i in [:env.header.moduleNames.size] do
    if selected env.header.moduleNames[i]! then
      for name in env.header.moduleData[i]!.constNames do
        names := names.insert name
  names := env.constants.foldStage2 (fun names name _ =>
    if selected name then names.insert name else names) names
  for name in names.toArray do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration {name} is missing from the checked environment"
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Checked {names.size} actual complete-DVR prime norm-residue and Milnor declarations: \
    standard axioms only."
