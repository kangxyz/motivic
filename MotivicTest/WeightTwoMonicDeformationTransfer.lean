/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightTwo.MonicDeformationTransfer
public import Lean.Util.CollectAxioms

/-!
# Consumers of complete arbitrary-unit endpoint transfers

The units below are independent. Repeated polynomials, colliding two-coordinate
images, and negative cycle coefficients use the same original maximal quotients
and their unreduced localization lengths.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial Motivic
open WeightTwoCorestriction WeightTwoMonicDeformation WeightTwoMonicDeformationTransfer
open scoped BigOperators

universe u

namespace MotivicTest.WeightTwoMonicDeformationTransfer

variable {k : Type u} [Field k]

/-- The canonical field structure on a maximal quotient used by these consumers. -/
local instance quotientField {R : Type u} [CommRing R] (q : MaximalSpectrum R) :
    Field (R ⧸ q.asIdeal) := Ideal.Quotient.field q.asIdeal

/-- Both entries are the literal images of independent original units. -/
theorem actual_two_unit_endpoint (p : k[X]) (hp : p.Monic)
    (a b : (AdjoinRoot p)ˣ) :
    letI := hp.finite_adjoinRoot
    letI : IsArtinianRing (AdjoinRoot p) := .of_finite k _
    letI : Fintype (MaximalSpectrum (AdjoinRoot p)) := Fintype.ofFinite _
    polynomialCycle p hp a b = ∑ q : MaximalSpectrum (AdjoinRoot p),
      ((Module.length (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal)).toNat : ℤ) •
        pointPushforward (k := k) ((Cor.graphFunctor (AdjoinRoot p ⧸ q.asIdeal)).map
          (WeightTwoSymbols.rationalPair (AdjoinRoot p ⧸ q.asIdeal)
            (Units.map (Ideal.Quotient.mk q.asIdeal).toMonoidHom a)
            (Units.map (Ideal.Quotient.mk q.asIdeal).toMonoidHom b))) :=
  polynomialCycle_eq_sum_pointPushforward p hp a b

/-- A repeated endpoint retains the original square algebra and its local lengths. -/
theorem repeated_endpoint (p : k[X]) (hp : p.Monic)
    (a b : (AdjoinRoot (p ^ 2))ˣ) :
    letI := (hp.pow 2).finite_adjoinRoot
    letI : IsArtinianRing (AdjoinRoot (p ^ 2)) := .of_finite k _
    letI : Fintype (MaximalSpectrum (AdjoinRoot (p ^ 2))) := Fintype.ofFinite _
    WeightTwoSymbols.cycleClass k (polynomialCycle (p ^ 2) (hp.pow 2) a b) =
      ∑ q : MaximalSpectrum (AdjoinRoot (p ^ 2)),
        ((Module.length (Localization.AtPrime q.asIdeal)
          (Localization.AtPrime q.asIdeal)).toNat : ℤ) •
          corestriction (k := k) (WeightTwoSymbols.graphSymbol (AdjoinRoot (p ^ 2) ⧸ q.asIdeal)
            (residueUnit (p ^ 2) a q) (residueUnit (p ^ 2) b q)) :=
  cycleClass_polynomialCycle_eq_sum_corestriction (p ^ 2) (hp.pow 2) a b

/-- Even identical unit coordinates do not merge or discard the original quotient sources. -/
theorem colliding_unit_coordinates (p : k[X]) (hp : p.Monic) :
    letI := hp.finite_adjoinRoot
    letI : IsArtinianRing (AdjoinRoot p) := .of_finite k _
    letI : Fintype (MaximalSpectrum (AdjoinRoot p)) := Fintype.ofFinite _
    polynomialCycle p hp 1 1 = ∑ q : MaximalSpectrum (AdjoinRoot p),
      ((Module.length (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal)).toNat : ℤ) •
        pointPushforward (k := k) ((Cor.graphFunctor (AdjoinRoot p ⧸ q.asIdeal)).map
          (WeightTwoSymbols.rationalPair (AdjoinRoot p ⧸ q.asIdeal) 1 1)) := by
  simpa only [residueUnit, map_one] using polynomialCycle_eq_sum_pointPushforward p hp 1 1

/-- Signed cycles retain all original quotient multiplicities in raw H22. -/
theorem signed_endpoint (p : k[X]) (hp : p.Monic)
    (a b : (AdjoinRoot p)ˣ) (n : ℤ) :
    letI := hp.finite_adjoinRoot
    letI : IsArtinianRing (AdjoinRoot p) := .of_finite k _
    letI : Fintype (MaximalSpectrum (AdjoinRoot p)) := Fintype.ofFinite _
    WeightTwoSymbols.cycleClass k (n • polynomialCycle p hp a b) =
      ∑ q : MaximalSpectrum (AdjoinRoot p),
        (n * (Module.length (Localization.AtPrime q.asIdeal)
          (Localization.AtPrime q.asIdeal)).toNat : ℤ) •
          corestriction (k := k) (WeightTwoSymbols.graphSymbol (AdjoinRoot p ⧸ q.asIdeal)
            (residueUnit p a q) (residueUnit p b q)) := by
  classical
  let := hp.finite_adjoinRoot
  let : IsArtinianRing (AdjoinRoot p) := .of_finite k _
  let : Fintype (MaximalSpectrum (AdjoinRoot p)) := Fintype.ofFinite _
  rw [map_zsmul, cycleClass_polynomialCycle_eq_sum_corestriction, Finset.smul_sum]
  simp only [smul_smul]

open Lean in
run_cmd do
  for name in #[``toIntegralCycle_retainedQuotientCycle, ``retainedPolynomialCycle_eq_sum,
      ``quotientRetainedMap_pair, ``retainedQuotientCycle_comp_forgetRoot,
      ``polynomialCycle_eq_sum_pointPushforward,
      ``cycleClass_polynomialCycle_eq_sum_corestriction,
      ``actual_two_unit_endpoint, ``repeated_endpoint, ``colliding_unit_coordinates,
      ``signed_endpoint] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Whole arbitrary-unit endpoint transfers use only standard foundations."

end MotivicTest.WeightTwoMonicDeformationTransfer
