/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.KTheory.MilnorK.PolynomialNormPrimeSubfieldInduction
import Lean.Util.CollectAxioms

/-! Direct original-map consumer with the explicit lower-degree induction premise. -/

namespace MotivicTest.GeneralMilnorPrimeSubfieldInduction

open Motivic.KTheory.MilnorK Polynomial Polynomial.LocalResidue
open Motivic.KTheory.MilnorK.PolynomialNorm
open Motivic.KTheory.MilnorK.PolynomialResidue

variable {k : Type*} [Field k] [CharZero k]

/-- No unconditional presentation-independence claim is made: the smaller-degree
premise is explicit, while the normal-prime tower itself is already proved. -/
theorem original_map_induction_step
    (p : MonicIrreducible k) [Normal k (AdjoinRoot p.val)]
    (hp : p.val.natDegree.Prime) (h₁ h₂ : MonicIrreducible k)
    (e : AdjoinRoot h₁.val ≃ₐ[k] AdjoinRoot h₂.val)
    (f : AdjoinRoot p.val →ₐ[k] AdjoinRoot h₁.val) (n : ℕ)
    (ih : ∀ (r s : MonicIrreducible (AdjoinRoot p.val)),
      r.val.natDegree < h₁.val.natDegree →
      ∀ (ε : AdjoinRoot r.val ≃ₐ[AdjoinRoot p.val] AdjoinRoot s.val)
        (y : K (AdjoinRoot r.val) n),
        polynomialNorm n s (map n ε.toRingHom y) = polynomialNorm n r y) :
    (polynomialNorm n h₂).comp (map n e.toRingHom) = polynomialNorm n h₁ := by
  apply LinearMap.ext
  exact polynomialNorm_map_algEquiv_of_prime_subfield_of_lower_degrees p hp h₁ h₂ e f n ih

end MotivicTest.GeneralMilnorPrimeSubfieldInduction

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`Motivic.KTheory.MilnorK,
    `MotivicTest.GeneralMilnorPrimeSubfieldInduction]
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
  logInfo m!"Checked {names.size} prime-subfield induction and Milnor declarations: \
    standard axioms only."
