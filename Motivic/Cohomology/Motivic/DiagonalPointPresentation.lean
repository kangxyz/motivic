/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.DiagonalPointNorm
public import Motivic.Cohomology.Motivic.DiagonalScalarTupleChange

/-!
# Exact whole-support presentations of diagonal point generators

Every actual integral finite support is the finite pushforward of its rational
coordinate tuple over its own full field of global functions. The canonical
support chart preserves the original scalar map, every original Laurent unit,
and the entire closed immersion before passing to cycles or homology. The
construction works in all characteristics and includes the empty tuple.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent

universe u

namespace Motivic.DiagonalPointPresentation

open DiagonalPointNorm DiagonalCycleSymbols DiagonalCorestriction
open WeightOneInterpolationCycle WeightTwoCubicBoundary
open WeightTwoCorestriction (torusMap torusMap_projection torusMap_coordinate
  torusPower_scheme_hom_ext rationalTorusPoint_scalar)

variable {k : Type u} [Field k] {q : ℕ} (Z : Generator k q)

/-- The literal projection to a specified original Laurent coordinate. -/
def coordinateProjection (i : Fin q) : Z.scheme ⟶ (SmoothSite.torus (.of k)).left :=
  Z.targetProjection ≫ (SmoothSite.torusCoordinate (.of k) q i).left

/-- Every Laurent coordinate retains the original support scalar action. -/
theorem coordinateProjection_structure (i : Fin q) :
    coordinateProjection Z i ≫ (SmoothSite.torus (.of k)).hom = Z.projection := by
  rw [coordinateProjection, Category.assoc,
    MorphismProperty.Over.w (SmoothSite.torusCoordinate (.of k) q i)]
  have h := Z.projection_base.symm
  change _ = Z.projection ≫ 𝟙 _ at h
  simpa only [Category.comp_id] using h

/-- Each original coordinate pulls back by evaluation at its original unit. -/
theorem coordinatePullback_eq_eval (i : Fin q) :
    affinePullback (coordinateProjection Z i) =
      LaurentPolynomial.eval₂ (scalarMap Z) (coordinateUnit Z i) := by
  apply laurentRingHom_ext
  · have hs := congrArg affinePullback (coordinateProjection_structure Z i)
    change affinePullback (coordinateProjection Z i ≫
      Spec.map (CommRingCat.ofHom LaurentPolynomial.C)) = scalarMap Z at hs
    rw [affinePullback_comp] at hs
    apply RingHom.ext
    intro r
    exact (RingHom.congr_fun hs r).trans (LaurentPolynomial.eval₂_C _ _ r).symm
  · simp only [LaurentPolynomial.eval₂_T, zpow_one]
    rfl

/-- The canonical affine chart presents the actual pullback of any affine map. -/
theorem supportIsoSpec_inv_map {R : Type u} [CommRing R]
    (f : Z.scheme ⟶ Spec (.of R)) :
    (supportIsoSpec Z).inv ≫ f =
      Spec.map (CommRingCat.ofHom (affinePullback f)) := by
  rw [supportIsoSpec, ← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv,
    ← Spec.map_comp]
  rfl

/-- The same support chart retains each of the original Laurent units. -/
@[reassoc] theorem supportIsoSpec_inv_coordinate (i : Fin q) :
    (supportIsoSpec Z).inv ≫ coordinateProjection Z i =
      unitMap (algebraMap k (coordinateRing Z)) (coordinateUnit Z i) := by
  rw [supportIsoSpec_inv_map, coordinatePullback_eq_eval]
  rfl

/-- The full tuple map, not just its coordinate images, is unchanged by the chart. -/
@[reassoc] theorem supportIsoSpec_inv_targetProjection :
    (supportIsoSpec Z).inv ≫ Z.targetProjection =
      (rationalTuple (coordinateRing Z) q (coordinateUnit Z)).left ≫
        torusMap (k := k) q := by
  apply torusPower_scheme_hom_ext q
  · rw [Category.assoc]
    have hZ : Z.targetProjection ≫ (SmoothSite.torusPower (.of k) q).hom =
        Z.projection := by
      have h := Z.projection_base.symm
      change _ = Z.projection ≫ 𝟙 _ at h
      simpa only [Category.comp_id] using h
    rw [hZ, supportIsoSpec_inv_projection, Category.assoc, torusMap_projection]
    have h := MorphismProperty.Over.w
      (rationalTuple (coordinateRing Z) q (coordinateUnit Z))
    change (rationalTuple (coordinateRing Z) q (coordinateUnit Z)).left ≫
      (SmoothSite.torusPower (coordinateRing Z) q).hom = 𝟙 _ at h
    erw [← Category.assoc, h, Category.id_comp]
  · intro i
    simp only [Category.assoc, torusMap_coordinate]
    have h := congrArg (fun f => f.left)
      (SmoothSite.torusPowerLift_coordinate (coordinateRing Z) q
        (fun j => WeightOnePointNorm.rationalTorusPoint (coordinateRing Z)
          (coordinateUnit Z j)) i)
    dsimp only [MorphismProperty.Comma.comp_left] at h
    change (rationalTuple (coordinateRing Z) q (coordinateUnit Z)).left ≫
      (SmoothSite.torusCoordinate (coordinateRing Z) q i).left = _ at h
    erw [← Category.assoc (rationalTuple (coordinateRing Z) q (coordinateUnit Z)).left,
      h, rationalTorusPoint_scalar]
    exact supportIsoSpec_inv_coordinate Z i

/-- The canonical chart identifies the original entire closed immersion exactly. -/
@[reassoc] theorem supportIsoSpec_inv_inclusion :
    (supportIsoSpec Z).inv ≫ Z.inclusion =
      finitePointMap (k := k) q
        (rationalTuple (coordinateRing Z) q (coordinateUnit Z)) := by
  apply pullback.hom_ext
  · rw [Category.assoc, finitePointMap_fst]
    exact supportIsoSpec_inv_projection Z
  · rw [Category.assoc, finitePointMap_snd]
    exact supportIsoSpec_inv_targetProjection Z

/-- Every original generator is the actual transfer from its own full support field. -/
theorem generator_cycle_eq_pointPushforward :
    Z.cycle = pointPushforward (k := k) q
      ((Cor.graphFunctor (coordinateRing Z)).map
        (rationalTuple (coordinateRing Z) q (coordinateUnit Z))) := by
  have : IsNoetherian ((𝟭 Scheme).obj (SmoothSite.base (Spec (.of k))).left) :=
    inferInstanceAs (IsNoetherian (Spec (.of k)))
  have : IsNoetherian Z.scheme := isNoetherian_of_finiteType Z.projection
  have : IsNoetherian
      (pullback (SmoothSite.base (Spec (.of k))).hom
        (SmoothSite.torusPower (.of k) q).hom) :=
    isNoetherian_of_finiteType (pullback.fst (SmoothSite.base (Spec (.of k))).hom
      (SmoothSite.torusPower (.of k) q).hom)
  apply FiniteCorrespondence.toIntegralCycle_injective
  rw [toIntegralCycle_pointPushforward_graph]
  simp only [← supportIsoSpec_inv_inclusion Z,
    IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply,
    finitePushforward_fundamentalCycle, FiniteCorrespondenceGenerator.cycle,
    FiniteCorrespondence.toIntegralCycle_single]
  exact (closedFundamentalCycle_of_isIntegral Z.val).symm

/-- The raw generator class is the genuine corestriction of its original tuple. -/
theorem cycleClass_generator :
    cycleClass k q Z.cycle =
      corestriction (k := k) q
        (graphSymbol (coordinateRing Z) q (coordinateUnit Z)) := by
  rw [generator_cycle_eq_pointPushforward, ← corestriction_cycleClass]
  rfl

variable (k) (q)

/-- All original signed coefficients are preserved in the whole-support presentation. -/
theorem cycle_eq_sum_pointPushforward
    (α : WeightOnePointNorm.point k ⟶ target k q) :
    α = α.sum (fun Z n => n • pointPushforward (k := k) q
      ((Cor.graphFunctor (coordinateRing Z)).map
        (rationalTuple (coordinateRing Z) q (coordinateUnit Z)))) := by
  classical
  conv_lhs => rw [← α.sum_single]
  apply Finset.sum_congr rfl
  intro Z _
  dsimp only
  erw [← generator_cycle_eq_pointPushforward]
  change Finsupp.single Z (Finsupp.toFun α Z) =
    Finsupp.toFun α Z • (Finsupp.single Z 1 : Generator k q →₀ ℤ)
  simp only [Finsupp.smul_single, smul_eq_mul, mul_one]

/-- The original raw cycle class retains every signed finite support. -/
theorem cycleClass_eq_sum_corestriction
    (α : WeightOnePointNorm.point k ⟶ target k q) :
    cycleClass k q α = α.sum (fun Z n => n • corestriction (k := k) q
      (graphSymbol (coordinateRing Z) q (coordinateUnit Z))) := by
  classical
  conv_lhs => rw [cycle_eq_sum_pointPushforward k q α]
  rw [map_finsuppSum]
  apply Finset.sum_congr rfl
  intro Z _
  dsimp only
  erw [map_zsmul, ← corestriction_cycleClass]
  rfl

/-- Every actual raw diagonal class is a signed sum of genuine whole-field transfers. -/
theorem exists_sum_corestriction (x : (motivicRawBaseComplex k q).homology q) :
    ∃ α : WeightOnePointNorm.point k ⟶ target k q,
      x = α.sum (fun Z n => n • corestriction (k := k) q
        (graphSymbol (coordinateRing Z) q (coordinateUnit Z))) := by
  obtain ⟨α, rfl⟩ := cycleClass_surjective k q x
  exact ⟨α, cycleClass_eq_sum_corestriction k q α⟩

end Motivic.DiagonalPointPresentation
