/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.KTheory.MilnorK.DedekindResiduePushforward
import Lean.Util.CollectAxioms

/-! Actual original-point residue pushforward and transitive standard axiom audit. -/

noncomputable section
namespace MotivicTest.GeneralMilnorDedekindPushforward
open Motivic.KTheory.MilnorK IsLocalRing AdicCompletion IsDedekindDomain
attribute [local instance] Classical.decEq

universe u
variable (A S F E : Type u) [CommRing A] [IsDedekindDomain A]
  [CommRing S] [IsDedekindDomain S] [Algebra A S] [Module.Finite A S]
  [Module.IsTorsionFree A S]
  [Field F] [CharZero F] [Algebra A F] [IsFractionRing A F]
  [Field E] [Algebra S E] [IsFractionRing S E]
  [Algebra A E] [IsScalarTower A S E]
  [Algebra F E] [IsScalarTower A F E] [FiniteDimensional F E]
  (p : HeightOneSpectrum A) [CharZero (ResidueField (Localization.AtPrime p.asIdeal))]

/-- Direct consumer expands every original residue norm and field map. -/
theorem actual_original_point_pushforward (n : ℕ) (x : K E (n + 1)) :
    letI := fun q : IdealBranch (p.asIdeal.map (algebraMap A S)) =>
      Localization.basePrimeLocalAlgebra p.asIdeal q.val
        (Localization.originalIdealBranch_under p q)
    letI := fun q : IdealBranch (p.asIdeal.map (algebraMap A S)) =>
      Localization.basePrimeLocal_isLocalHom p.asIdeal q.val
        (Localization.originalIdealBranch_under p q)
    letI := fun q : IdealBranch (p.asIdeal.map (algebraMap A S)) =>
      Localization.basePrimeLocal_residueFinite p.asIdeal q.val
        (Localization.originalIdealBranch_under p q)
    letI := fun q : IdealBranch (p.asIdeal.map (algebraMap A S)) =>
      originalBranchFractionAlgebra S E q
    letI := fun q : IdealBranch (p.asIdeal.map (algebraMap A S)) =>
      originalBranchIsFractionRing S E q
    DVR.residue (Localization.AtPrime p.asIdeal) F n
      (finiteExtensionNorm F E (n + 1) x) =
      ∑ q : IdealBranch (p.asIdeal.map (algebraMap A S)),
        finiteExtensionNorm (ResidueField (Localization.AtPrime p.asIdeal))
          (ResidueField (Localization.AtPrime q.val)) n
            (DVR.residue (Localization.AtPrime q.val) E n x) :=
  residue_finiteExtensionNorm_atPrime A S F E p n x

end MotivicTest.GeneralMilnorDedekindPushforward

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`AdjoinRoot, `Motivic.KTheory.MilnorK,
    `MotivicTest.GeneralMilnorDedekindPushforward]
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
  logInfo m!"Checked {names.size} original Dedekind pushforward declarations: \
    standard axioms only."
