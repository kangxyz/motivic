/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.KTheory.MilnorK.PolynomialNormDVRTrace
import Lean.Util.CollectAxioms

/-! An actual unramified-class consumer of the all-degree Galois trace formula. -/

open Polynomial
open Motivic.KTheory.MilnorK Motivic.KTheory.MilnorK.PolynomialResidue
open Motivic.KTheory.MilnorK.PolynomialNorm

namespace MotivicTest.GeneralMilnorPolynomialNormDVRTrace

variable {F : Type*} [Field F] [CharZero F]
  (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Algebra R F] [IsFractionRing R F]
  (p : MonicIrreducible F)
  (S : Type*) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Algebra S (AdjoinRoot p.val)]
  [IsScalarTower R S (AdjoinRoot p.val)]
  [IsFractionRing S (AdjoinRoot p.val)] [IsIntegralClosure S R (AdjoinRoot p.val)]
  [Normal F (AdjoinRoot p.val)] [IsLocalHom (algebraMap R S)]

/-- An unramified input gives a ramification-annihilated restricted output
residue. This does not silently conclude that the output itself is unramified. -/
theorem unramified_class_trace (n : ℕ) (x : K (AdjoinRoot p.val) (n + 1))
    (hx : DVR.residue S (AdjoinRoot p.val) n x = 0)
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e) :
    (e : ℤ) • map n (IsLocalRing.ResidueField.map (algebraMap R S))
        (DVR.residue R F n (polynomialNorm (n + 1) p x)) = 0 := by
  rw [residue_polynomialNorm_galois_trace R p S n x hπ hϖ u e he]
  simp [hx]

end MotivicTest.GeneralMilnorPolynomialNormDVRTrace

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`Motivic.KTheory.MilnorK,
    `MotivicTest.GeneralMilnorPolynomialNormDVRTrace]
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
  logInfo m!"Checked {names.size} Galois trace and Milnor declarations: \
    standard axioms only."
