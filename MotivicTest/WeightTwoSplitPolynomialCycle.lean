/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightTwo.SplitPolynomialCycle
public import Mathlib.Algebra.Field.ZMod
public import Lean.Util.CollectAxioms

/-!
# Consumers of whole weight-two split polynomial cycles

The generic sum and doubled-root tests are equalities of actual finite
correspondences before homology. A characteristic-three cubic test checks
that the nonreduced quotient keeps all three copies of its rational pair.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open _root_.AlgebraicGeometry.Scheme (fundamentalCycle)
open _root_.AlgebraicGeometry.Scheme (IntegralCycle)
open CategoryTheory AlgebraicGeometry Polynomial Motivic
open Polynomial.TwoUnitPolynomialFamily
open Motivic.WeightTwoCubicBoundary Motivic.WeightTwoSymbols
open Motivic.WeightTwoSplitPolynomialCycle
open scoped BigOperators

universe u

namespace MotivicTest.WeightTwoSplitPolynomialCycle

variable {k : Type u} [Field k]

/-- Each original maximal quotient contributes its unaltered local length. -/
theorem actual_whole_graph_sum (p : k[X]) (hp : p.Monic)
    (h0 : IsUnit (p.eval 0)) (h1 : IsUnit (p.eval 1))
    (a b : MaximalSpectrum (AdjoinRoot p) → kˣ)
    (ha : ∀ q, Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root p) =
      algebraMap k (AdjoinRoot p ⧸ q.asIdeal) (a q : k))
    (hb : ∀ q, (b q : k) = 1 - (a q : k)) :
    letI := hp.finite_adjoinRoot
    letI : IsArtinianRing (AdjoinRoot p) := .of_finite k _
    letI : Fintype (MaximalSpectrum (AdjoinRoot p)) := Fintype.ofFinite _
    polynomialCycle p hp h0 h1 = ∑ q : MaximalSpectrum (AdjoinRoot p),
      ((Module.length (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal)).toNat : ℤ) •
        (Cor.graphFunctor k).map (rationalPair k (a q) (b q)) :=
  polynomialCycle_eq_sum_graph p hp h0 h1 a b ha hb

/-- Equal roots are counted twice, in any characteristic. -/
theorem actual_double_root (a b : kˣ)
    (h0 : IsUnit (((X - C (a : k)) * (X - C (a : k))).eval 0))
    (h1 : IsUnit (((X - C (a : k)) * (X - C (a : k))).eval 1))
    (hb : (b : k) = 1 - (a : k)) :
    polynomialCycle ((X - C (a : k)) * (X - C (a : k)))
      (WeightOneSplitPolynomialCycle.twoLinear_monic a a) h0 h1 =
        (2 : ℤ) • (Cor.graphFunctor k).map (rationalPair k a b) :=
  polynomialCycle_double_root a b h0 h1 hb

/-- Forgetting admissibility retains the complete nonreduced doubled fundamental cycle. -/
theorem actual_double_fundamental_cycle (a b : kˣ)
    (h0 : IsUnit (((X - C (a : k)) * (X - C (a : k))).eval 0))
    (h1 : IsUnit (((X - C (a : k)) * (X - C (a : k))).eval 1))
    (hb : (b : k) = 1 - (a : k)) :
    IntegralCycle.finitePushforward
      (polynomialInclusion ((X - C (a : k)) * (X - C (a : k))) h0 h1)
      (fundamentalCycle (Spec (.of
        (AdjoinRoot ((X - C (a : k)) * (X - C (a : k))))))) =
      FiniteCorrespondence.toIntegralCycle
        ((2 : ℤ) • (Cor.graphFunctor k).map (rationalPair k a b)) := by
  exact (toIntegralCycle_polynomialCycle _
    (WeightOneSplitPolynomialCycle.twoLinear_monic a a) h0 h1).symm.trans
      (congrArg FiniteCorrespondence.toIntegralCycle (polynomialCycle_double_root a b h0 h1 hb))

/-- Every scalar linear factor contributes its actual pair graph, allowing any collisions. -/
theorem actual_three_graph_sum (a a' b b' c c' : kˣ)
    (h0 : IsUnit (((X - C (a : k)) * (X - C (b : k)) * (X - C (c : k))).eval 0))
    (h1 : IsUnit (((X - C (a : k)) * (X - C (b : k)) * (X - C (c : k))).eval 1))
    (ha' : (a' : k) = 1 - (a : k)) (hb' : (b' : k) = 1 - (b : k))
    (hc' : (c' : k) = 1 - (c : k)) :
    polynomialCycle ((X - C (a : k)) * (X - C (b : k)) * (X - C (c : k)))
      (AdjoinRoot.three_linear_monic (a : k) b c) h0 h1 =
        (Cor.graphFunctor k).map (rationalPair k a a') +
          (Cor.graphFunctor k).map (rationalPair k b b') +
          (Cor.graphFunctor k).map (rationalPair k c c') :=
  polynomialCycle_threeLinear a a' b b' c c' h0 h1 ha' hb' hc'

/-- When two factors coincide, the entire original quotient retains coefficient two. -/
theorem actual_colliding_last_factors (a a' b b' : kˣ)
    (h0 : IsUnit (((X - C (a : k)) * (X - C (b : k)) * (X - C (b : k))).eval 0))
    (h1 : IsUnit (((X - C (a : k)) * (X - C (b : k)) * (X - C (b : k))).eval 1))
    (ha' : (a' : k) = 1 - (a : k)) (hb' : (b' : k) = 1 - (b : k)) :
    polynomialCycle ((X - C (a : k)) * (X - C (b : k)) * (X - C (b : k)))
      (AdjoinRoot.three_linear_monic (a : k) b b) h0 h1 =
        (Cor.graphFunctor k).map (rationalPair k a a') +
          (2 : ℤ) • (Cor.graphFunctor k).map (rationalPair k b b') := by
  rw [polynomialCycle_threeLinear a a' b b' b b' h0 h1 ha' hb' hb']
  abel

/-- Three coalesced factors retain every nilpotent contribution in any characteristic. -/
theorem actual_colliding_all_factors (a a' : kˣ)
    (h0 : IsUnit (((X - C (a : k)) * (X - C (a : k)) * (X - C (a : k))).eval 0))
    (h1 : IsUnit (((X - C (a : k)) * (X - C (a : k)) * (X - C (a : k))).eval 1))
    (ha' : (a' : k) = 1 - (a : k)) :
    polynomialCycle ((X - C (a : k)) * (X - C (a : k)) * (X - C (a : k)))
      (AdjoinRoot.three_linear_monic (a : k) a a) h0 h1 =
        (3 : ℤ) • (Cor.graphFunctor k).map (rationalPair k a a') := by
  rw [polynomialCycle_threeLinear a a' a a' a a' h0 h1 ha' ha' ha']
  abel

/-- A literal factorization transports directly to actual raw graph classes. -/
theorem actual_factored_graph_symbols (p : k[X]) (hp : p.Monic)
    (h0 : IsUnit (p.eval 0)) (h1 : IsUnit (p.eval 1)) (a a' b b' c c' : kˣ)
    (hfactor : p = (X - C (a : k)) * (X - C (b : k)) * (X - C (c : k)))
    (ha' : (a' : k) = 1 - (a : k)) (hb' : (b' : k) = 1 - (b : k))
    (hc' : (c' : k) = 1 - (c : k)) :
    cycleClass k (polynomialCycle p hp h0 h1) =
      graphSymbol k a a' + graphSymbol k b b' + graphSymbol k c c' :=
  cycleClass_eq_three_graphSymbol_of_factorization p hp h0 h1 a a' b b' c c'
    hfactor ha' hb' hc'

/-- The canonical field structure on a maximal quotient used by these consumers. -/
local instance quotientField {R : Type u} [CommRing R] (q : MaximalSpectrum R) :
    Field (R ⧸ q.asIdeal) := Ideal.Quotient.field q.asIdeal

/-- Every original residue of this inseparable cubic has the scalar root two. -/
theorem characteristic_three_residual_root
    (q : MaximalSpectrum (AdjoinRoot (cubicZero (2 : ZMod 3)))) :
    Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root (cubicZero (2 : ZMod 3))) =
      algebraMap (ZMod 3) (AdjoinRoot (cubicZero (2 : ZMod 3)) ⧸ q.asIdeal) 2 := by
  let : CharP (AdjoinRoot (cubicZero (2 : ZMod 3)) ⧸ q.asIdeal) 3 :=
    charP_of_injective_algebraMap
      (algebraMap (ZMod 3) (AdjoinRoot (cubicZero (2 : ZMod 3)) ⧸ q.asIdeal)).injective 3
  have h := congrArg (Ideal.Quotient.mk q.asIdeal)
    (AdjoinRoot.eval₂_root (cubicZero (2 : ZMod 3)))
  simp only [cubicZero, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, map_pow] at h
  apply sub_eq_zero.mp
  apply eq_zero_of_pow_eq_zero (n := 3)
  rw [sub_pow_char]
  exact h

/-- The entire characteristic-three cubic is three times its actual rational graph. -/
theorem characteristic_three_triple_graph :
    zeroCycle (2 : ZMod 3) (by decide) (by decide) =
      (3 : ℤ) • (Cor.graphFunctor (ZMod 3)).map
        (rationalPair (ZMod 3) (Units.mk0 2 (by decide)) (Units.mk0 2 (by decide))) := by
  unfold zeroCycle
  rw [polynomialCycle_eq_degree_smul_graph _ _ _ _
    (Units.mk0 2 (by decide)) (Units.mk0 2 (by decide)) characteristic_three_residual_root
      (by decide)]
  have hd : (cubicZero (2 : ZMod 3)).natDegree = 3 := by
    unfold cubicZero
    compute_degree; norm_num
  rw [hd]
  rfl

/-- The nonreduced cubic multiplicity also survives passage to actual raw homology. -/
theorem characteristic_three_triple_symbol :
    cycleClass (ZMod 3) (zeroCycle (2 : ZMod 3) (by decide) (by decide)) =
      (3 : ℤ) • graphSymbol (ZMod 3) (Units.mk0 2 (by decide)) (Units.mk0 2 (by decide)) := by
  rw [characteristic_three_triple_graph, map_zsmul]
  rfl

end MotivicTest.WeightTwoSplitPolynomialCycle

open Lean in
run_cmd do
  for name in #[
      `Motivic.WeightTwoSplitPolynomialCycle.pairMap_eq_rationalPair,
      `Motivic.WeightTwoSplitPolynomialCycle.polynomialQuotient_target,
      `Motivic.WeightTwoSplitPolynomialCycle.graph_eq_single,
      `Motivic.WeightTwoSplitPolynomialCycle.polynomialQuotient_support,
      `Motivic.WeightTwoSplitPolynomialCycle.polynomialCycle_eq_sum_graph,
      `Motivic.WeightTwoSplitPolynomialCycle.polynomialCycle_eq_degree_smul_graph,
      `Motivic.WeightTwoSplitPolynomialCycle.polynomialCycle_double_root,
      `Motivic.WeightTwoSplitPolynomialCycle.cycleClass_polynomialCycle_eq_sum_graphSymbol,
      `Motivic.WeightTwoSplitPolynomialCycle.polynomialCycle_twoRoots_degree_three,
      `Motivic.WeightTwoSplitPolynomialCycle.polynomialCycle_threeRoots_of_local_length,
      `Motivic.WeightTwoSplitPolynomialCycle.polynomialCycle_threeLinear,
      `Motivic.WeightTwoSplitPolynomialCycle.polynomialCycle_eq_three_graph_of_factorization,
      `Motivic.WeightTwoSplitPolynomialCycle.cycleClass_eq_three_graphSymbol_of_factorization,
      `Motivic.WeightTwoSplitPolynomialCycle.zeroCycle_eq_sum_graph,
      `Motivic.WeightTwoSplitPolynomialCycle.oneCycle_eq_sum_graph,
      `Motivic.WeightTwoSplitPolynomialCycle.cubic_graphSymbol_relation,
      `MotivicTest.WeightTwoSplitPolynomialCycle.actual_whole_graph_sum,
      `MotivicTest.WeightTwoSplitPolynomialCycle.actual_double_root,
      `MotivicTest.WeightTwoSplitPolynomialCycle.actual_double_fundamental_cycle,
      `MotivicTest.WeightTwoSplitPolynomialCycle.actual_three_graph_sum,
      `MotivicTest.WeightTwoSplitPolynomialCycle.actual_colliding_last_factors,
      `MotivicTest.WeightTwoSplitPolynomialCycle.actual_colliding_all_factors,
      `MotivicTest.WeightTwoSplitPolynomialCycle.actual_factored_graph_symbols,
      `MotivicTest.WeightTwoSplitPolynomialCycle.characteristic_three_residual_root,
      `MotivicTest.WeightTwoSplitPolynomialCycle.characteristic_three_triple_graph,
      `MotivicTest.WeightTwoSplitPolynomialCycle.characteristic_three_triple_symbol] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Whole weight-two split polynomial cycles use only standard Lean foundations."
