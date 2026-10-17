/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.KTheory.MilnorK.PolynomialNormRationalFunction
import Lean.Util.CollectAxioms

/-! Direct consumers on the original rational-function groups. -/

namespace MotivicTest.GeneralMilnorPolynomialNormRationalFunction

open Motivic.KTheory.MilnorK Polynomial Polynomial.LocalResidue
open Motivic.KTheory.MilnorK.PolynomialResidue
open Motivic.KTheory.MilnorK.PolynomialNorm

variable {k : Type*} [Field k] [CharZero k]

/-- Constants use the original norm, with the original field embeddings. -/
theorem original_constant_square (n : ℕ) (p : MonicIrreducible k) :
    (rationalFunctionNorm n p).comp (map n RatFunc.C) =
      (map n RatFunc.C).comp (polynomialNorm n p) := by
  apply LinearMap.ext
  exact rationalFunctionNorm_map_C n p

/-- Inversion is literal on both rational-function fields. -/
theorem original_inversion_square (n : ℕ) (p : MonicIrreducible k) :
    (map n (RatFunc.inversion k).toRingHom).comp (rationalFunctionNorm n p) =
      (rationalFunctionNorm n p).comp
        (map n (RatFunc.inversion (AdjoinRoot p.val)).toRingHom) := by
  apply LinearMap.ext
  exact rationalFunctionNorm_inversion n p

end MotivicTest.GeneralMilnorPolynomialNormRationalFunction

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`Motivic.KTheory.MilnorK,
    `MotivicTest.GeneralMilnorPolynomialNormRationalFunction]
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
  logInfo m!"Checked {names.size} actual rational norm and Milnor declarations: \
    standard axioms only."
