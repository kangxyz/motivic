/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Motivic.KTheory.MilnorK.NormalizedCurveReciprocity
import Lean.Util.CollectAxioms

/-! # Reciprocity on the original finite model and every original infinity branch -/

noncomputable section

namespace MotivicTest.GeneralMilnorCurveReciprocity
open Motivic.KTheory.MilnorK Motivic.KTheory.MilnorK.DedekindResidue

open Polynomial IsLocalRing IsDedekindDomain

universe u
variable (k S E : Type u) [Field k] [CharZero k]
  [CommRing S] [IsDedekindDomain S] [Algebra k[X] S] [Module.Finite k[X] S]
  [Module.IsTorsionFree k[X] S] [Algebra k S] [IsScalarTower k k[X] S]
  [Field E] [Algebra S E] [IsFractionRing S E]
  [Algebra k[X] E] [IsScalarTower k[X] S E]
  [Algebra (RatFunc k) E] [IsScalarTower k[X] (RatFunc k) E]
  [FiniteDimensional (RatFunc k) E]

open scoped Classical in
/-- Reciprocity for a finite Dedekind model of the affine line, including every
branch of its original function field above infinity. -/
theorem actual_original_curve_sum (n : ℕ) (x : K E (n + 1)) :
    letI : Algebra.FiniteType k S := Algebra.FiniteType.trans (S := k[X])
      (inferInstanceAs (Algebra.FiniteType k k[X]))
      (inferInstanceAs (Algebra.FiniteType k[X] S))
    letI : ∀ q : HeightOneSpectrum S,
        FiniteDimensional k (ResidueField (Localization.AtPrime q.asIdeal)) :=
      fun q => Localization.finiteType_localResidue_finite k S q.asIdeal
    (∑ q ∈ (totalResidue S E n x).support,
      finiteExtensionNorm k (ResidueField (Localization.AtPrime q.asIdeal)) n
        (DVR.residue (Localization.AtPrime q.asIdeal) E n x)) +
      infinityBranchResidueSum k E n x = 0 := by
  let : Algebra.FiniteType k S := Algebra.FiniteType.trans (S := k[X])
    (inferInstanceAs (Algebra.FiniteType k k[X]))
    (inferInstanceAs (Algebra.FiniteType k[X] S))
  let : ∀ q : HeightOneSpectrum S,
      FiniteDimensional k (ResidueField (Localization.AtPrime q.asIdeal)) :=
    fun q => Localization.finiteType_localResidue_finite k S q.asIdeal
  rw [← normedTotalResidue_eq_sum]
  exact normalized_curve_reciprocity k S E n x

end MotivicTest.GeneralMilnorCurveReciprocity

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`AdjoinRoot, `Motivic.KTheory.MilnorK,
    `MotivicTest.GeneralMilnorCurveReciprocity]
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
  logInfo m!"Checked {names.size} original curve reciprocity declarations: \
    standard axioms only."
