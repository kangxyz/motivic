/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.KTheory.MilnorK.PolynomialNormPrimeInduction
import Lean.Util.CollectAxioms

/-! Consumers for the nonnormal prime induction step. Every occurrence of the
smaller-degree presentation-independence hypothesis remains visible. -/

open Polynomial
open Motivic.KTheory.MilnorK Motivic.KTheory.MilnorK.PolynomialResidue
open Motivic.KTheory.MilnorK.PolynomialNorm

namespace MotivicTest.GeneralMilnorPolynomialNormPrimeInduction

variable {k : Type*} [Field k] [CharZero k]

/-- The root-field induction hypothesis gives an actual annihilator over k,
without assuming the original extension is normal. -/
theorem actual_degree_annihilator (n : ℕ) (p q : MonicIrreducible k)
    (hp : 1 < p.val.natDegree) (e : AdjoinRoot p.val ≃ₐ[k] AdjoinRoot q.val)
    (ih : ∀ (r s : MonicIrreducible (AdjoinRoot p.val)),
      r.val.natDegree < p.val.natDegree →
      ∀ (ε : AdjoinRoot r.val ≃ₐ[AdjoinRoot p.val] AdjoinRoot s.val)
        (y : K (AdjoinRoot r.val) n),
        polynomialNorm n s (map n ε.toRingHom y) = polynomialNorm n r y)
    (x : K (AdjoinRoot p.val) n) :
    (p.val.natDegree : ℤ) •
      (polynomialNorm n q (map n e.toRingHom x) - polynomialNorm n p x) = 0 :=
  polynomialNorm_degree_smul_sub_eq_zero_of_lower_degrees n p q hp e ih x

/-- Combining the proven annihilator with a finite coprime mixed restriction
closes the prime step for arbitrary classes, not only individual symbols. -/
theorem nonnormal_prime_step (n : ℕ) (p q : MonicIrreducible k)
    (hp : p.val.natDegree.Prime) (e : AdjoinRoot p.val ≃ₐ[k] AdjoinRoot q.val)
    (ih : ∀ (r s : MonicIrreducible (AdjoinRoot p.val)),
      r.val.natDegree < p.val.natDegree →
      ∀ (ε : AdjoinRoot r.val ≃ₐ[AdjoinRoot p.val] AdjoinRoot s.val)
        (y : K (AdjoinRoot r.val) n),
        polynomialNorm n s (map n ε.toRingHom y) = polynomialNorm n r y)
    (x : K (AdjoinRoot p.val) n) :
    polynomialNorm n q (map n e.toRingHom x) = polynomialNorm n p x :=
  polynomialNorm_map_algEquiv_of_prime_of_lower_degrees n p q hp e ih x

end MotivicTest.GeneralMilnorPolynomialNormPrimeInduction

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`Motivic.KTheory.MilnorK,
    `MotivicTest.GeneralMilnorPolynomialNormPrimeInduction]
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
  logInfo m!"Checked {names.size} prime induction and Milnor declarations: \
    standard axioms only."
