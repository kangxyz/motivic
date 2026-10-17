/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.KTheory.MilnorK.FiniteExtensionNormDVR
import Lean.Util.CollectAxioms

/-! Original-field and original-branch norm-residue consumer and axiom audit. -/

noncomputable section

namespace MotivicTest.GeneralMilnorDVRNorm
open Motivic.KTheory.MilnorK
open IsLocalRing AdicCompletion
open scoped TensorProduct

universe u
variable (R S F E : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CharZero (ResidueField R)]
  [CommRing S] [IsDedekindDomain S] [Algebra R S] [Module.Finite R S]
  [Module.IsTorsionFree R S] [DecidableEq (Ideal S)]
  [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra R E] [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
  [Algebra F E] [IsScalarTower R F E] [FiniteDimensional F E]


/-- Direct original-field consumer of every original valuation branch. -/
theorem actual_original_dvr_sum (n : ℕ) (x : K E (n + 1)) :
    letI := fun q : IdealBranch ((maximalIdeal R).map (algebraMap R S)) =>
      originalBranchFractionAlgebra S E q
    letI := fun q : IdealBranch ((maximalIdeal R).map (algebraMap R S)) =>
      originalBranchIsFractionRing S E q
    DVR.residue R F n (finiteExtensionNorm F E (n + 1) x) =
      ∑ q : IdealBranch ((maximalIdeal R).map (algebraMap R S)),
        finiteExtensionNorm (ResidueField R) (ResidueField (Localization.AtPrime q.val)) n
          (DVR.residue (Localization.AtPrime q.val) E n x) :=
  residue_finiteExtensionNorm_dvr R S F E n x

end MotivicTest.GeneralMilnorDVRNorm

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`AdjoinRoot, `Motivic.KTheory.MilnorK,
    `MotivicTest.GeneralMilnorDVRNorm]
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
  logInfo m!"Checked {names.size} original DVR norm-residue declarations: \
    standard axioms only."
