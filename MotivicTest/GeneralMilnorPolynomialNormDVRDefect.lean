/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.KTheory.MilnorK.PolynomialNormDVRDefect
import Lean.Util.CollectAxioms

/-! Direct all-class consumer of the actual norm-residue degree annihilator. -/

open Polynomial
open Motivic.KTheory.MilnorK Motivic.KTheory.MilnorK.PolynomialResidue
open Motivic.KTheory.MilnorK.PolynomialNorm

namespace MotivicTest.GeneralMilnorPolynomialNormDVRDefect

variable {F : Type*} [Field F] [CharZero F]
  (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Algebra R F] [IsFractionRing R F]
  (p : MonicIrreducible F)
  (S : Type*) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Algebra S (AdjoinRoot p.val)]
  [IsScalarTower R S (AdjoinRoot p.val)]
  [IsFractionRing S (AdjoinRoot p.val)] [IsIntegralClosure S R (AdjoinRoot p.val)]
  [Normal F (AdjoinRoot p.val)] [IsLocalHom (algebraMap R S)]
  [Module.Finite R S] [Module.IsTorsionFree R S]
  [CharZero (IsLocalRing.ResidueField R)]

/-- The original polynomial degree kills the actual residue difference on an
arbitrary class, with no mixedness, prime-degree or norm-tower hypothesis. -/
theorem actual_degree_annihilator (n : ℕ) (x : K (AdjoinRoot p.val) (n + 1))
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
    (q : MonicIrreducible (IsLocalRing.ResidueField R))
    (ε : AdjoinRoot q.val ≃ₐ[IsLocalRing.ResidueField R] IsLocalRing.ResidueField S) :
    (p.val.natDegree : ℤ) •
      (DVR.residue R F n (polynomialNorm (n + 1) p x) -
        polynomialNorm n q (map n ε.symm.toRingHom
          (DVR.residue S (AdjoinRoot p.val) n x))) = 0 :=
  degree_smul_residue_polynomialNorm_defect R p S n x hπ hϖ u e he q ε

end MotivicTest.GeneralMilnorPolynomialNormDVRDefect

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`Motivic.KTheory.MilnorK,
    `MotivicTest.GeneralMilnorPolynomialNormDVRDefect]
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
  logInfo m!"Checked {names.size} DVR defect and Milnor declarations: \
    standard axioms only."
