/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightTwo.CubicBoundary
public import Motivic.Cohomology.WeightTwo.CorestrictionMixed
public import Aglib.RingTheory.AdjoinRootNormEvaluation

/-!
# Whole polynomial cycles as actual finite transfers

Every maximal quotient of the original monic polynomial algebra contributes its
literal root-complement graph over its actual quotient field. The original
local lengths remain the coefficients, including nilpotents and inseparable
residue extensions. The comparison is first an equality of affine scheme maps,
then an equality of actual finite cycle pushforwards, and finally an equality
in the original weight-two raw homology.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open Polynomial.TwoUnitPolynomialFamily
open scoped BigOperators

universe u

namespace Motivic.WeightTwoPolynomialTransfer
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Hom

open _root_.AlgebraicGeometry.Scheme.FiniteAlgebra
open _root_.Motivic.WeightOneFundamentalNorm
open WeightTwoCubicBoundary
open WeightTwoCorestriction

variable {k : Type u} [Field k]

/-- The field structure on `R ⧸ q.asIdeal` supplied by maximality of `q`. -/
local instance quotientField {R : Type u} [CommRing R] (q : MaximalSpectrum R) :
    Field (R ⧸ q.asIdeal) := Ideal.Quotient.field q.asIdeal

/-- The original root unit, mapped by the actual maximal quotient homomorphism. -/
def residueRootUnit (p : k[X]) (h0 : IsUnit (p.eval 0))
    (q : MaximalSpectrum (AdjoinRoot p)) : (AdjoinRoot p ⧸ q.asIdeal)ˣ :=
  Units.map (Ideal.Quotient.mk q.asIdeal).toMonoidHom (rootUnit p h0)

/-- The original complement unit, with the same quotient and scalar maps. -/
def residueComplementUnit (p : k[X]) (h1 : IsUnit (p.eval 1))
    (q : MaximalSpectrum (AdjoinRoot p)) : (AdjoinRoot p ⧸ q.asIdeal)ˣ :=
  Units.map (Ideal.Quotient.mk q.asIdeal).toMonoidHom (oneSubRootUnit p h1)

/-- The two residue coordinates are literally complementary in the original field. -/
theorem residueComplementUnit_val (p : k[X])
    (h0 : IsUnit (p.eval 0)) (h1 : IsUnit (p.eval 1))
    (q : MaximalSpectrum (AdjoinRoot p)) :
    (residueComplementUnit p h1 q : AdjoinRoot p ⧸ q.asIdeal) =
      1 - (residueRootUnit p h0 q : AdjoinRoot p ⧸ q.asIdeal) := by
  change Ideal.Quotient.mk q.asIdeal (1 - AdjoinRoot.root p) =
    1 - Ideal.Quotient.mk q.asIdeal (AdjoinRoot.root p)
  rw [map_sub, map_one]

/-- Scalar restriction preserves both actual coordinates of a rational pair. -/
theorem rationalPair_torusMap {E : Type u} [Field E] [Algebra k E] (a b : Eˣ) :
    (WeightTwoSymbols.rationalPair E a b).left ≫ torusMap (k := k) 2 =
      pairMap (algebraMap k E) a b := by
  apply pair_hom_ext
  · rw [pairMap_first, Category.assoc, torusMap_coordinate, ← Category.assoc,
      rationalPair_coordinate_left]
    exact rationalTorusPoint_scalar a
  · rw [pairMap_second, Category.assoc, torusMap_coordinate, ← Category.assoc,
      rationalPair_coordinate_right]
    exact rationalTorusPoint_scalar b

/-- Both original affine coordinates agree before any cycle or homology quotient. -/
theorem polynomialQuotient_scalarPoint (p : k[X])
    (h0 : IsUnit (p.eval 0)) (h1 : IsUnit (p.eval 1))
    (q : MaximalSpectrum (AdjoinRoot p)) :
    quotientMap q ≫ polynomialInclusion p h0 h1 =
      scalarPoint (k := k) (WeightTwoSymbols.rationalPair (AdjoinRoot p ⧸ q.asIdeal)
        (residueRootUnit p h0 q) (residueComplementUnit p h1 q)) := by
  apply pullback.hom_ext
  · rw [Category.assoc, polynomialInclusion_fst, scalarPoint_fst]
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl
  · rw [Category.assoc, polynomialInclusion_snd, scalarPoint_snd, rationalPair_torusMap]
    exact pairMap_comp (AdjoinRoot.of p)
      (algebraMap k (AdjoinRoot p ⧸ q.asIdeal)) (Ideal.Quotient.mk q.asIdeal)
      (rootUnit p h0) (oneSubRootUnit p h1)
      (residueRootUnit p h0 q) (residueComplementUnit p h1 q) rfl rfl rfl

/-- A literal maximal quotient pushes to its original reduced support with coefficient one. -/
theorem finitePushforward_quotientMap {R : Type u} [CommRing R]
    (q : MaximalSpectrum R) :
    IntegralCycle.finitePushforward (quotientMap q)
      (fundamentalCycle (Spec (.of (R ⧸ q.asIdeal)))) =
      Finsupp.single (quotientSupport q) 1 := by
  rw [fundamentalCycle_of_isIntegral, IntegralCycle.finitePushforward_single,
    residueDegree_of_surjectiveOnStalks, Nat.cast_one, mul_one]
  congr 1
  apply IntegralClosedSubscheme.point_injective
  rw [IntegralClosedSubscheme.point_finiteImage,
    IntegralClosedSubscheme.point_pointClosure, quotientMap_genericPoint, quotientSupport_point]

/-- Each branch is precisely the existing finite transfer, before passing to homology. -/
theorem polynomialQuotient_pushforward (p : k[X]) (hp : p.Monic)
    (h0 : IsUnit (p.eval 0)) (h1 : IsUnit (p.eval 1))
    (q : MaximalSpectrum (AdjoinRoot p)) :
    letI := hp.finite_adjoinRoot
    IntegralCycle.finitePushforward (polynomialInclusion p h0 h1)
      (Finsupp.single (quotientSupport q) 1) =
      FiniteCorrespondence.toIntegralCycle
        (pointPushforward (k := k) ((Cor.graphFunctor (AdjoinRoot p ⧸ q.asIdeal)).map
          (WeightTwoSymbols.rationalPair (AdjoinRoot p ⧸ q.asIdeal)
            (residueRootUnit p h0 q) (residueComplementUnit p h1 q)))) := by
  let := hp.finite_adjoinRoot
  rw [← finitePushforward_quotientMap, ← AddMonoidHom.comp_apply,
    ← IntegralCycle.finitePushforward_comp, toIntegralCycle_pointPushforward_graph,
    IntegralCycle.finitePushforward_congr (polynomialQuotient_scalarPoint p h0 h1 q)]
  rfl

/-- The whole polynomial cycle is the sum of actual transfers from every original
maximal quotient, weighted by the original unreduced local lengths. -/
theorem polynomialCycle_eq_sum_pointPushforward (p : k[X]) (hp : p.Monic)
    (h0 : IsUnit (p.eval 0)) (h1 : IsUnit (p.eval 1)) :
    letI := hp.finite_adjoinRoot
    letI : IsArtinianRing (AdjoinRoot p) := .of_finite k _
    letI : Fintype (MaximalSpectrum (AdjoinRoot p)) := Fintype.ofFinite _
    polynomialCycle p hp h0 h1 = ∑ q : MaximalSpectrum (AdjoinRoot p),
      ((Module.length (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal)).toNat : ℤ) •
        pointPushforward (k := k) ((Cor.graphFunctor (AdjoinRoot p ⧸ q.asIdeal)).map
          (WeightTwoSymbols.rationalPair (AdjoinRoot p ⧸ q.asIdeal)
            (residueRootUnit p h0 q) (residueComplementUnit p h1 q))) := by
  classical
  let := hp.finite_adjoinRoot
  let : IsArtinianRing (AdjoinRoot p) := .of_finite k _
  let : Fintype (MaximalSpectrum (AdjoinRoot p)) := Fintype.ofFinite _
  apply FiniteCorrespondence.toIntegralCycle_injective
  rw [toIntegralCycle_polynomialCycle, fundamentalCycle_affine_eq_sum (k := k), map_sum,
    map_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [map_zsmul, ← polynomialQuotient_pushforward p hp h0 h1 q, ← map_zsmul]
  congr 1
  simp only [Finsupp.smul_single, smul_eq_mul, mul_one]

/-- The decomposition descends through the existing cycle class and actual finite
corestriction on the original weight-two raw homology. -/
theorem cycleClass_polynomialCycle_eq_sum_corestriction (p : k[X]) (hp : p.Monic)
    (h0 : IsUnit (p.eval 0)) (h1 : IsUnit (p.eval 1)) :
    letI := hp.finite_adjoinRoot
    letI : IsArtinianRing (AdjoinRoot p) := .of_finite k _
    letI : Fintype (MaximalSpectrum (AdjoinRoot p)) := Fintype.ofFinite _
    WeightTwoSymbols.cycleClass k (polynomialCycle p hp h0 h1) =
      ∑ q : MaximalSpectrum (AdjoinRoot p),
        ((Module.length (Localization.AtPrime q.asIdeal)
          (Localization.AtPrime q.asIdeal)).toNat : ℤ) •
          corestriction (k := k) (WeightTwoSymbols.graphSymbol (AdjoinRoot p ⧸ q.asIdeal)
            (residueRootUnit p h0 q) (residueComplementUnit p h1 q)) := by
  classical
  let := hp.finite_adjoinRoot
  let : IsArtinianRing (AdjoinRoot p) := .of_finite k _
  let : Fintype (MaximalSpectrum (AdjoinRoot p)) := Fintype.ofFinite _
  rw [polynomialCycle_eq_sum_pointPushforward p hp h0 h1, map_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [map_zsmul, ← corestriction_cycleClass]
  rfl

/-- The complement norms use the same full collection of maximal quotient fields
and the same original local lengths as the cycle decomposition. -/
theorem prod_residueComplement_norm_eq_eval_one (p : k[X]) (hp : p.Monic)
    (h1 : IsUnit (p.eval 1)) :
    letI := hp.finite_adjoinRoot
    letI : IsArtinianRing (AdjoinRoot p) := .of_finite k _
    letI : Fintype (MaximalSpectrum (AdjoinRoot p)) := Fintype.ofFinite _
    (∏ q : MaximalSpectrum (AdjoinRoot p),
      Algebra.norm k (residueComplementUnit p h1 q : AdjoinRoot p ⧸ q.asIdeal) ^
        (Module.length (Localization.AtPrime q.asIdeal)
          (Localization.AtPrime q.asIdeal)).toNat) = p.eval 1 := by
  classical
  let := hp.finite_adjoinRoot
  let : IsArtinianRing (AdjoinRoot p) := .of_finite k _
  let : Fintype (MaximalSpectrum (AdjoinRoot p)) := Fintype.ofFinite _
  change (∏ q : MaximalSpectrum (AdjoinRoot p),
    Algebra.norm k (Ideal.Quotient.mk q.asIdeal (1 - AdjoinRoot.root p)) ^
      (Module.length (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal)).toNat) = p.eval 1
  exact (Algebra.norm_eq_prod_quotient_norm_pow_local_length
    (k := k) (1 - AdjoinRoot.root p)).symm.trans (AdjoinRoot.norm_one_sub_root p hp)

end Motivic.WeightTwoPolynomialTransfer
