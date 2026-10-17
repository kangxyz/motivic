/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.KTheory.MilnorK.PolynomialNormIndependence
import Lean.Util.CollectAxioms

/-! Unconditional original-map consumers: arbitrary polynomial degrees and all Milnor degrees. -/

namespace MotivicTest.GeneralMilnorPolynomialNormIndependence

open Motivic.KTheory.MilnorK Polynomial Polynomial.LocalResidue
open Motivic.KTheory.MilnorK.PolynomialNorm
open Motivic.KTheory.MilnorK.PolynomialResidue

variable {k : Type*} [Field k] [CharZero k]

/-- No normality, prime degree, induction premise, or norm compatibility input. -/
theorem original_general_norm_map (n : ℕ) (p q : MonicIrreducible k)
    (e : AdjoinRoot p.val ≃ₐ[k] AdjoinRoot q.val) :
    (polynomialNorm n q).comp (map n e.toRingHom) = polynomialNorm n p :=
  polynomialNorm_comp_map_algEquiv n p q e

/-- Degree zero is included without an extra positivity premise. -/
theorem original_degree_zero (p q : MonicIrreducible k)
    (e : AdjoinRoot p.val ≃ₐ[k] AdjoinRoot q.val) (x : K (AdjoinRoot p.val) 0) :
    polynomialNorm 0 q (map 0 e.toRingHom x) = polynomialNorm 0 p x :=
  polynomialNorm_map_algEquiv 0 p q e x

/-- The inverse presentation change recovers the original norm on every class. -/
theorem original_inverse_presentation (n : ℕ) (p q : MonicIrreducible k)
    (e : AdjoinRoot p.val ≃ₐ[k] AdjoinRoot q.val) (y : K (AdjoinRoot q.val) n) :
    polynomialNorm n p (map n e.symm.toRingHom y) = polynomialNorm n q y :=
  polynomialNorm_map_algEquiv n q p e.symm y

end MotivicTest.GeneralMilnorPolynomialNormIndependence

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`Motivic.KTheory.MilnorK,
    `MotivicTest.GeneralMilnorPolynomialNormIndependence]
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
  logInfo m!"Checked {names.size} general polynomial norm independence and Milnor declarations: \
    standard axioms only."
