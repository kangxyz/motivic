/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Motivic.KTheory.MilnorK.PolynomialResidueCompleteCoefficient
import Lean.Util.CollectAxioms

/-! The original upper rational map and actual integral closure, with no
postulated local map, residue isomorphism or compatibility assumption. -/

open Polynomial Polynomial.LocalResidue
open Motivic.KTheory.MilnorK Motivic.KTheory.MilnorK.PolynomialResidue
open Motivic.KTheory.MilnorK.PolynomialNorm
open Motivic.KTheory.MilnorK.PolynomialNorm.CompleteCoefficientResidue
open Motivic.PowerSeriesConstantClosure

namespace MotivicTest.GeneralMilnorPolynomialResidueCompleteCoefficient

variable {k : Type*} [Field k] [CharZero k] (p : MonicIrreducible k)

local instance : Fact (Irreducible (X : (AdjoinRoot p.val)[X])) := ⟨irreducible_X⟩

/-- The localization sends the original rational variable to the literal
power-series parameter inside the actual integral closure. -/
theorem actual_local_uniformizer :
    upperLocalMap p (algebraMap (AdjoinRoot p.val)[X]
      (Ring (X : (AdjoinRoot p.val)[X])) X) =
        algebraMap (PowerSeries k) (Closure p) PowerSeries.X :=
  coefficientDVRLocalMap_X _ _ _ _ _

/-- The upper residue square uses exactly the field map already occurring in
the original polynomial norm's completion base change. -/
theorem original_completion_map_square (n : ℕ)
    (x : K (RatFunc (AdjoinRoot p.val)) (n + 1)) :
    map n (residueEquiv p).symm.toRingHom
      (DVR.residue (Closure p) (TopField p) n
        (map (n + 1) (rationalCompletionRootMap p (constantPolynomial p)
          (constantPolynomial_eq_rationalCoefficient_map p)) x)) =
        map n (InfinityResidue.rootXEquiv (AdjoinRoot p.val)).toRingHom
          (residueAt (X : (AdjoinRoot p.val)[X]) n x) := by
  rw [← upperFieldMap_eq_rationalCompletionRootMap]
  exact upper_residue_square p n x

end MotivicTest.GeneralMilnorPolynomialResidueCompleteCoefficient

open Lean in
run_cmd do
  let env ← getEnv
  let names := #[
    `Polynomial.LocalResidue.coefficientDVRLocalMap,
    `Polynomial.LocalResidue.coefficientDVRLocalMap_isLocalHom,
    `Polynomial.LocalResidue.coefficientDVRLocalMap_fraction,
    `Motivic.KTheory.MilnorK.PolynomialNorm.rationalCoefficientLaurentMap,
    `Motivic.KTheory.MilnorK.PolynomialNorm.rationalCoefficientLaurentMap_C,
    `Motivic.KTheory.MilnorK.PolynomialNorm.rationalCoefficientLaurentMap_X,
    `Motivic.KTheory.MilnorK.PolynomialNorm.rationalCoefficientLaurentMap_fractionMap,
    `Motivic.KTheory.MilnorK.PolynomialNorm.CompleteCoefficientResidue.upperLocalMap,
    `Motivic.KTheory.MilnorK.PolynomialNorm.CompleteCoefficientResidue.upperLocalMap_fraction,
    `Motivic.KTheory.MilnorK.PolynomialNorm.CompleteCoefficientResidue.upper_residue_square,
    `MotivicTest.GeneralMilnorPolynomialResidueCompleteCoefficient.actual_local_uniformizer,
    `MotivicTest.GeneralMilnorPolynomialResidueCompleteCoefficient.original_completion_map_square]
  for name in names do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration {name} is missing from the checked environment"
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Checked the actual upper complete-coefficient residue square: standard axioms only."
