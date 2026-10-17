/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.KTheory.MilnorK.FiniteExtensionNormCompletePGroup
import Lean.Util.CollectAxioms

/-! Actual p-group local square without any residue-law hypothesis. -/

namespace MotivicTest.GeneralMilnorFiniteExtensionNormCompletePGroup

open Motivic.KTheory.MilnorK IsLocalRing

universe u

/-- Complete-DVR compatibility for every extension embedded in a Galois p-group. -/
theorem actual_pgroup_complete_square
    (R S F E Ω : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (maximalIdeal R) R] [CharZero (ResidueField R)]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field F] [CharZero F] [Field E] [CharZero E] [Field Ω]
    [Algebra R F] [IsFractionRing R F]
    [Algebra F E] [FiniteDimensional F E] [Algebra R E] [IsScalarTower R F E]
    [Algebra R S] [Module.Finite R S] [IsLocalHom (algebraMap R S)]
    [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
    [IsIntegralClosure S R E]
    [Algebra F Ω] [FiniteDimensional F Ω] [IsGalois F Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (hG : IsPGroup ℓ (Ω ≃ₐ[F] Ω)) (g : E →ₐ[F] Ω)
    (n : ℕ) (x : K E (n + 1)) :
    DVR.residue R F n (finiteExtensionNorm F E (n + 1) x) =
      finiteExtensionNorm (ResidueField R) (ResidueField S) n (DVR.residue S E n x) :=
  residue_finiteExtensionNorm_complete_of_pGroup R S F E Ω ℓ hG g n x

end MotivicTest.GeneralMilnorFiniteExtensionNormCompletePGroup

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`AdjoinRoot, `Motivic.KTheory.MilnorK,
    `MotivicTest.GeneralMilnorFiniteExtensionNormCompletePGroup]
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
  logInfo m!"Checked {names.size} complete-DVR p-group and Milnor declarations: \
    standard axioms only."
