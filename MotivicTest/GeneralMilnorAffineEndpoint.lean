/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.KTheory.MilnorK.AffineEndpointNormEquality
import Motivic.KTheory.MilnorK.DVRValueCartierLength
import Lean.Util.CollectAxioms

/-! Actual endpoint equality, full multiplicity, and standard-foundation audit. -/

noncomputable section
namespace MotivicTest.GeneralMilnorAffineEndpoint
open Motivic.KTheory.MilnorK Motivic.KTheory.MilnorK.DedekindResidue Polynomial
universe u
variable (k S E : Type u) [Field k] [CharZero k]
  [CommRing S] [IsDedekindDomain S] [Algebra k[X] S] [Module.Finite k[X] S]
  [Module.IsTorsionFree k[X] S]
  [Field E] [Algebra S E] [IsFractionRing S E]
  [Algebra k[X] E] [IsScalarTower k[X] S E]
  [Algebra (RatFunc k) E] [IsScalarTower k[X] (RatFunc k) E]
  [FiniteDimensional (RatFunc k) E]

/-- The full original endpoint branch sums agree, with no boundary premise. -/
theorem actual_zero_one_endpoint_sum (n : ℕ) (u : Fin (n + 1) → Sˣ) :
    endpointWeightedResidueSum k S E 0 (n + 1) u =
      endpointWeightedResidueSum k S E 1 (n + 1) u :=
  endpointWeightedResidueSum_eq k S E 0 1 n u

end MotivicTest.GeneralMilnorAffineEndpoint

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`AdjoinRoot, `Motivic.KTheory.MilnorK, `Motivic.KTheory.MilnorK2.DVR,
    `MotivicTest.GeneralMilnorAffineEndpoint]
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
  logInfo m!"Checked {names.size} original weighted endpoint declarations: \
    standard axioms only."
