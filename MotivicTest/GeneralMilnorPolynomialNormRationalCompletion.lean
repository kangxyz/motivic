/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.KTheory.MilnorK.PolynomialNormRationalCompletion
import Lean.Util.CollectAxioms

/-! Direct consumer of the literal complete root-field norm restriction. -/

namespace MotivicTest.GeneralMilnorPolynomialNormRationalCompletion

open Motivic.KTheory.MilnorK Polynomial Polynomial.LocalResidue
open Motivic.KTheory.MilnorK.PolynomialNorm
open Motivic.KTheory.MilnorK.PolynomialResidue
open scoped RatFunc

variable {k : Type*} [Field k] [CharZero k]

/-- The map on the original rational-function Milnor group is retained. -/
theorem original_completion_square (n : ℕ) (p : MonicIrreducible k)
    (q : MonicIrreducible (LaurentSeries k))
    (hq : q.val = (rationalCoefficientPolynomial p).val.map
      (algebraMap (RatFunc k) (LaurentSeries k))) :
    (map n (algebraMap (RatFunc k) (LaurentSeries k))).comp (rationalFunctionNorm n p) =
      (polynomialNorm n q).comp (map n (rationalCompletionRootMap p q hq)) := by
  apply LinearMap.ext
  exact rationalFunctionNorm_restrict_completion n p q hq

end MotivicTest.GeneralMilnorPolynomialNormRationalCompletion

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`Motivic.KTheory.MilnorK,
    `MotivicTest.GeneralMilnorPolynomialNormRationalCompletion]
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
  logInfo m!"Checked {names.size} rational completion and Milnor declarations: \
    standard axioms only."
