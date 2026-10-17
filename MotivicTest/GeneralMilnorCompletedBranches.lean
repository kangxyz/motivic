/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.KTheory.MilnorK.PolynomialNormCompletedBranches
import Lean.Util.CollectAxioms

/-! Actual full completed branch sum and residue completion identity. -/

namespace MotivicTest.GeneralMilnorCompletedBranches

open Motivic.KTheory.MilnorK Polynomial PolynomialNorm PolynomialResidue
open Polynomial.LocalResidue AdjoinRoot IsLocalRing

attribute [local instance] PolynomialNorm.completionResidueCharZero
  PolynomialNorm.completionFractionCharZero

universe u

variable (R F : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CharZero (ResidueField R)] [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]

/-- Direct consumer retains every original completed factor and root map. -/
theorem actual_completed_branch_sum
    (p : MonicIrreducible F) (n : ℕ) (x : K (AdjoinRoot p.val) (n + 1)) :
    DVR.residue R F n (polynomialNorm (n + 1) p x) =
      map n (AdicCompletion.residueFieldEquiv R).toRingHom
        (∑ q ∈ (placesAbove (AdicCompletion.fractionRingMap R F) p).attach,
          completeBranchResidueNorm (AdicCompletion (maximalIdeal R) R)
            (FractionRing (AdicCompletion (maximalIdeal R) R)) q.val n
              (map (n + 1) (adjoinRootMap (AdicCompletion.fractionRingMap R F)
                p.val q.val.val ((mem_placesAbove _ _ _).mp q.property)) x)) :=
  residue_polynomialNorm_eq_completed_branch_sum R F p n x

/-- The original finite field and presentation transport remain visible. -/
theorem actual_original_field_completed_branch_sum
    (E : Type u) [Field E] [Algebra F E] [FiniteDimensional F E]
    (p : MonicIrreducible F) (ε : AdjoinRoot p.val ≃ₐ[F] E)
    (n : ℕ) (x : K E (n + 1)) :
    DVR.residue R F n (finiteExtensionNorm F E (n + 1) x) =
      map n (AdicCompletion.residueFieldEquiv R).toRingHom
        (∑ q ∈ (placesAbove (AdicCompletion.fractionRingMap R F) p).attach,
          completeBranchResidueNorm (AdicCompletion (maximalIdeal R) R)
            (FractionRing (AdicCompletion (maximalIdeal R) R)) q.val n
              (map (n + 1) ((adjoinRootMap (AdicCompletion.fractionRingMap R F)
                p.val q.val.val ((mem_placesAbove _ _ _).mp q.property)).comp
                  ε.symm.toRingHom) x)) :=
  residue_finiteExtensionNorm_eq_completed_branch_sum R F E p ε n x

end MotivicTest.GeneralMilnorCompletedBranches

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`AdjoinRoot, `Motivic.KTheory.MilnorK,
    `MotivicTest.GeneralMilnorCompletedBranches]
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
  logInfo m!"Checked {names.size} completed branch norm-residue declarations: \
    standard axioms only."
