/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightTwo.MonicDeformation
public import Motivic.Cohomology.WeightTwo.PolynomialTransfer
public import Motivic.AlgebraicGeometry.Correspondences.BaseChange.FinitePoint

/-!
# Exact finite transfers of arbitrary two-unit polynomial endpoints

Every maximal quotient of the original monic algebra contributes its original
two units with the original unreduced local length. The root is retained until
individual finite supports are postcomposed with the actual projection graph.
The ambient projection is not assumed finite. Distinct supports may have the
same two-coordinate image; their full residue degrees and integer sums remain.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open scoped BigOperators

universe u

namespace Motivic.WeightTwoMonicDeformationTransfer
open _root_.AlgebraicGeometry.Scheme

open _root_.AlgebraicGeometry.Scheme.FiniteAlgebra
open _root_.Motivic.WeightOneFundamentalNorm
open WeightTwoCorestriction
open WeightTwoMonicDeformation
open FiniteCorrespondenceGenerator

variable {k : Type u} [Field k]

local instance quotientField {R : Type u} [CommRing R] (q : MaximalSpectrum R) :
    Field (R ⧸ q.asIdeal) := Ideal.Quotient.field q.asIdeal

/-- A chosen original unit, mapped by the actual maximal quotient map. -/
def residueUnit (p : k[X]) (a : (AdjoinRoot p)ˣ)
    (q : MaximalSpectrum (AdjoinRoot p)) : (AdjoinRoot p ⧸ q.asIdeal)ˣ :=
  Units.map (Ideal.Quotient.mk q.asIdeal).toMonoidHom a

/-- The literal quotient point retaining the root and both original units. -/
def quotientRetainedMap (p : k[X]) (a b : (AdjoinRoot p)ˣ)
    (q : MaximalSpectrum (AdjoinRoot p)) :
    Spec (.of (AdjoinRoot p ⧸ q.asIdeal)) ⟶ pointAmbient k :=
  quotientMap q ≫ polynomialInclusion p a b

instance quotientRetainedMap_closed (p : k[X]) (a b : (AdjoinRoot p)ˣ)
    (q : MaximalSpectrum (AdjoinRoot p)) :
    IsClosedImmersion (quotientRetainedMap p a b q) := by
  unfold quotientRetainedMap
  infer_instance

@[reassoc (attr := simp)]
theorem quotientRetainedMap_fst (p : k[X]) (a b : (AdjoinRoot p)ˣ)
    (q : MaximalSpectrum (AdjoinRoot p)) :
    quotientRetainedMap p a b q ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap k (AdjoinRoot p ⧸ q.asIdeal))) := by
  rw [quotientRetainedMap, Category.assoc, polynomialInclusion_fst]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

instance quotientRetainedMap_projection_finite (p : k[X])
    [Module.Finite k (AdjoinRoot p)] (a b : (AdjoinRoot p)ˣ)
    (q : MaximalSpectrum (AdjoinRoot p)) :
    IsFinite (quotientRetainedMap p a b q ≫
      pullback.fst (SmoothSite.base (Spec (.of k))).hom (retainedTarget k).hom) := by
  rw [quotientRetainedMap_fst]
  exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

/-- The branch correspondence before forgetting its auxiliary root. -/
def retainedQuotientCycle (p : k[X]) (hp : p.Monic) (a b : (AdjoinRoot p)ˣ)
    (q : MaximalSpectrum (AdjoinRoot p)) :
    WeightOnePointNorm.point k ⟶ Cor.mk (retainedTarget k) :=
  letI := hp.finite_adjoinRoot
  weightedSupportImage k (Spec (.of (AdjoinRoot p ⧸ q.asIdeal)))
    (quotientRetainedMap p a b q)
    (FinitePointCorrespondenceBaseChange.range_projection (quotientRetainedMap p a b q))

/-- The branch still has the full pushed fundamental cycle of its actual quotient field. -/
theorem toIntegralCycle_retainedQuotientCycle (p : k[X]) (hp : p.Monic)
    (a b : (AdjoinRoot p)ˣ) (q : MaximalSpectrum (AdjoinRoot p)) :
    FiniteCorrespondence.toIntegralCycle (retainedQuotientCycle p hp a b q) =
      IntegralCycle.finitePushforward (quotientRetainedMap p a b q)
        (fundamentalCycle (Spec (.of (AdjoinRoot p ⧸ q.asIdeal)))) := by
  let := hp.finite_adjoinRoot
  exact toIntegralCycle_weightedSupportImage k _ _ _

/-- The retained endpoint is the sum over all original maximal quotients. -/
theorem retainedPolynomialCycle_eq_sum (p : k[X]) (hp : p.Monic)
    (a b : (AdjoinRoot p)ˣ) :
    letI := hp.finite_adjoinRoot
    letI : IsArtinianRing (AdjoinRoot p) := .of_finite k _
    letI : Fintype (MaximalSpectrum (AdjoinRoot p)) := Fintype.ofFinite _
    retainedPolynomialCycle p hp a b = ∑ q : MaximalSpectrum (AdjoinRoot p),
      ((Module.length (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal)).toNat : ℤ) • retainedQuotientCycle p hp a b q := by
  classical
  let := hp.finite_adjoinRoot
  let : IsArtinianRing (AdjoinRoot p) := .of_finite k _
  let : Fintype (MaximalSpectrum (AdjoinRoot p)) := Fintype.ofFinite _
  apply FiniteCorrespondence.toIntegralCycle_injective
  rw [toIntegralCycle_retainedPolynomialCycle, fundamentalCycle_affine_eq_sum (k := k),
    map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [map_zsmul, toIntegralCycle_retainedQuotientCycle]
  change IntegralCycle.finitePushforward (polynomialInclusion p a b) _ =
    _ • IntegralCycle.finitePushforward (quotientMap q ≫ polynomialInclusion p a b) _
  rw [IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply,
    WeightTwoPolynomialTransfer.finitePushforward_quotientMap, ← map_zsmul]
  congr 1
  simp only [Finsupp.smul_single, smul_eq_mul, mul_one]

/-- Forgetting the root gives literally the original two quotient-unit coordinates. -/
theorem quotientRetainedMap_pair (p : k[X]) (a b : (AdjoinRoot p)ˣ)
    (q : MaximalSpectrum (AdjoinRoot p)) :
    quotientRetainedMap p a b q ≫ pullback.snd _ _ ≫ (forgetRoot k).left =
      (WeightTwoSymbols.rationalPair (AdjoinRoot p ⧸ q.asIdeal)
        (residueUnit p a q) (residueUnit p b q)).left ≫ torusMap (k := k) 2 := by
  rw [WeightTwoPolynomialTransfer.rationalPair_torusMap]
  change quotientRetainedMap p a b q ≫ pullback.snd _ _ ≫ pullback.snd _ _ = _
  rw [quotientRetainedMap, Category.assoc, polynomialInclusion_snd_assoc,
    polynomialTargetMap_pair]
  exact WeightTwoCubicBoundary.pairMap_comp (AdjoinRoot.of p)
    (algebraMap k (AdjoinRoot p ⧸ q.asIdeal)) (Ideal.Quotient.mk q.asIdeal)
    a b (residueUnit p a q) (residueUnit p b q) rfl rfl rfl

/-- Postcomposition of each actual finite support is the original finite transfer.
Only its support map is finite; no finiteness of the ambient projection is used. -/
theorem retainedQuotientCycle_comp_forgetRoot (p : k[X]) (hp : p.Monic)
    (a b : (AdjoinRoot p)ˣ) (q : MaximalSpectrum (AdjoinRoot p)) :
    letI := hp.finite_adjoinRoot
    retainedQuotientCycle p hp a b q ≫ (Cor.graphFunctor k).map (forgetRoot k) =
      pointPushforward (k := k) ((Cor.graphFunctor (AdjoinRoot p ⧸ q.asIdeal)).map
        (WeightTwoSymbols.rationalPair (AdjoinRoot p ⧸ q.asIdeal)
          (residueUnit p a q) (residueUnit p b q))) := by
  let := hp.finite_adjoinRoot
  apply FiniteCorrespondence.toIntegralCycle_injective
  exact (supportLiftImageGenerator_graph k
    (Spec (.of (AdjoinRoot p ⧸ q.asIdeal))) (quotientRetainedMap p a b q)
    (FinitePointCorrespondenceBaseChange.range_projection (quotientRetainedMap p a b q))
    (forgetRoot k)
    (scalarPoint (k := k) (WeightTwoSymbols.rationalPair (AdjoinRoot p ⧸ q.asIdeal)
      (residueUnit p a q) (residueUnit p b q)))
    (by rw [scalarPoint_fst, quotientRetainedMap_fst])
    (by rw [scalarPoint_snd, quotientRetainedMap_pair])).trans
      (toIntegralCycle_pointPushforward_graph (k := k)
        (WeightTwoSymbols.rationalPair (AdjoinRoot p ⧸ q.asIdeal)
          (residueUnit p a q) (residueUnit p b q))).symm

/-- The whole two-unit endpoint is the sum of actual transfers, with every
original unreduced local length, even when branch images collide. -/
theorem polynomialCycle_eq_sum_pointPushforward (p : k[X]) (hp : p.Monic)
    (a b : (AdjoinRoot p)ˣ) :
    letI := hp.finite_adjoinRoot
    letI : IsArtinianRing (AdjoinRoot p) := .of_finite k _
    letI : Fintype (MaximalSpectrum (AdjoinRoot p)) := Fintype.ofFinite _
    polynomialCycle p hp a b = ∑ q : MaximalSpectrum (AdjoinRoot p),
      ((Module.length (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal)).toNat : ℤ) •
        pointPushforward (k := k) ((Cor.graphFunctor (AdjoinRoot p ⧸ q.asIdeal)).map
          (WeightTwoSymbols.rationalPair (AdjoinRoot p ⧸ q.asIdeal)
            (residueUnit p a q) (residueUnit p b q))) := by
  classical
  let := hp.finite_adjoinRoot
  let : IsArtinianRing (AdjoinRoot p) := .of_finite k _
  let : Fintype (MaximalSpectrum (AdjoinRoot p)) := Fintype.ofFinite _
  rw [polynomialCycle, retainedPolynomialCycle_eq_sum p hp a b, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro q _
  rw [Preadditive.zsmul_comp, retainedQuotientCycle_comp_forgetRoot]

/-- The exact full decomposition descends through the original cycle class and
actual corestriction on weight-two raw homology. -/
theorem cycleClass_polynomialCycle_eq_sum_corestriction (p : k[X]) (hp : p.Monic)
    (a b : (AdjoinRoot p)ˣ) :
    letI := hp.finite_adjoinRoot
    letI : IsArtinianRing (AdjoinRoot p) := .of_finite k _
    letI : Fintype (MaximalSpectrum (AdjoinRoot p)) := Fintype.ofFinite _
    WeightTwoSymbols.cycleClass k (polynomialCycle p hp a b) =
      ∑ q : MaximalSpectrum (AdjoinRoot p),
        ((Module.length (Localization.AtPrime q.asIdeal)
          (Localization.AtPrime q.asIdeal)).toNat : ℤ) •
          corestriction (k := k) (WeightTwoSymbols.graphSymbol (AdjoinRoot p ⧸ q.asIdeal)
            (residueUnit p a q) (residueUnit p b q)) := by
  classical
  let := hp.finite_adjoinRoot
  let : IsArtinianRing (AdjoinRoot p) := .of_finite k _
  let : Fintype (MaximalSpectrum (AdjoinRoot p)) := Fintype.ofFinite _
  rw [polynomialCycle_eq_sum_pointPushforward p hp a b, map_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [map_zsmul, ← corestriction_cycleClass]
  rfl

end Motivic.WeightTwoMonicDeformationTransfer
