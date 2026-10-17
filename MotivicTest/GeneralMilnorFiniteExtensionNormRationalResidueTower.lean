/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.KTheory.MilnorK.FiniteExtensionNormRationalResidueTower
import Lean.Util.CollectAxioms

/-! Actual rational residue sums compose under explicit lower and upper induction premises. -/

namespace MotivicTest.GeneralMilnorFiniteExtensionNormRationalResidueTower

open Motivic.KTheory.MilnorK Polynomial PolynomialResidue PolynomialNorm AdjoinRoot
open scoped RatFunc

attribute [local instance] Polynomial.algebra AdjoinRoot.scalarBranchAlgebra
  Motivic.KTheory.MilnorK.residueRootFinite Motivic.KTheory.MilnorK.residueRootCharZero
  Motivic.KTheory.MilnorK.primeRationalFinite

universe u

/-- Both finite-place square hypotheses remain visible in this honest induction step. -/
theorem original_residue_tower_induction
    {k L E : Type u} [Field k] [CharZero k] [Field L] [CharZero L] [Field E]
    [Algebra k L] [Algebra L E] [Algebra k E] [IsScalarTower k L E]
    [FiniteDimensional k L] [FiniteDimensional L E] [FiniteDimensional k E]
    (n : ℕ)
    (lower : ∀ h : MonicIrreducible k, ∀ y : K (RatFunc L) (n + 1),
      residueAt h.val n (finiteExtensionNorm (RatFunc k) (RatFunc L) (n + 1) y) =
        rationalResidueNormSum k L h n y)
    (upper : ∀ r : MonicIrreducible L, ∀ y : K (RatFunc E) (n + 1),
      residueAt r.val n (finiteExtensionNorm (RatFunc L) (RatFunc E) (n + 1) y) =
        rationalResidueNormSum L E r n y)
    (h : MonicIrreducible k) (x : K (RatFunc E) (n + 1)) :
    residueAt h.val n (finiteExtensionNorm (RatFunc k) (RatFunc E) (n + 1) x) =
      rationalResidueNormSum k E h n x :=
  residueAt_finiteExtensionNorm_rational_of_tower n lower upper h x

end MotivicTest.GeneralMilnorFiniteExtensionNormRationalResidueTower

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`AdjoinRoot, `Motivic.KTheory.MilnorK,
    `MotivicTest.GeneralMilnorFiniteExtensionNormRationalResidueTower]
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
  logInfo m!"Checked {names.size} actual rational residue tower induction and Milnor declarations: \
    standard axioms only."
