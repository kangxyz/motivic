/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.KTheory.MilnorK.PolynomialNormCompletePrime
import Lean.Util.CollectAxioms

/-! Direct all-class consumer of the complete prime-normal tame norm square. -/

namespace MotivicTest.GeneralMilnorPolynomialNormCompletePrime

open Motivic.KTheory.MilnorK Motivic.KTheory.MilnorK.PolynomialNorm
open Polynomial Polynomial.LocalResidue PolynomialResidue IsLocalRing
open Motivic.CompleteDVRExtension

universe u

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R] [CharZero (ResidueField R)]
  (F : Type u) [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]

/-- No mixedness or auxiliary valuation data is assumed for the original class. -/
theorem original_class_square
    (p : MonicIrreducible F) [Normal F (AdjoinRoot p.val)]
    (hp : p.val.natDegree.Prime) (n : ℕ) (x : K (AdjoinRoot p.val) (n + 1))
    (q : MonicIrreducible (ResidueField R)) :
    let _ := (AdjoinRoot.powerBasis p.property.2.ne_zero).finite
    let _ := integralClosure_isDiscreteValuationRing R F (AdjoinRoot p.val)
    let _ := integralClosure_isLocalHom R F (AdjoinRoot p.val)
    let _ := IsIntegralClosure.isFractionRing_of_finite_extension R F (AdjoinRoot p.val)
      (integralClosure R (AdjoinRoot p.val))
    ∀ ε : AdjoinRoot q.val ≃ₐ[ResidueField R] ResidueField (integralClosure R (AdjoinRoot p.val)),
      DVR.residue R F n (polynomialNorm (n + 1) p x) =
        polynomialNorm n q (map n ε.symm.toRingHom
          (DVR.residue (integralClosure R (AdjoinRoot p.val)) (AdjoinRoot p.val) n x)) :=
  residue_polynomialNorm_complete_prime R F p hp n x q

end MotivicTest.GeneralMilnorPolynomialNormCompletePrime

open Lean in
run_cmd do
  let env ← getEnv
  if env.header.isModule then
    throwError "This consumer requires legacy imports for its axiom check"
  let prefixes := #[`Motivic.KTheory.MilnorK,
    `MotivicTest.GeneralMilnorPolynomialNormCompletePrime]
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
  logInfo m!"Checked {names.size} complete prime norm and Milnor declarations: \
    standard axioms only."
