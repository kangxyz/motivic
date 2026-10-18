/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.DiagonalNormalizedEndpointCycles
public import Motivic.Cohomology.Motivic.DiagonalBoundaryFiberEvaluation
public import Motivic.Cohomology.Motivic.AffineEndpointGeometricNorm
public import Aglib.KTheory.MilnorK.Dedekind.AffineEndpointNormAllDegrees

/-! # Actual normalized endpoint norm evaluation of original simplex supports -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Polynomial
universe u
namespace Motivic.DiagonalBoundarySupport
variable {k : Type u} [Field k] [CharZero k] {q : ℕ} (Z : Generator k q)

omit [CharZero k] in
attribute [-instance] DiagonalPointNorm.coordinateField in
/-- The normalized endpoint retains every literal original global coordinate unit. -/
theorem normalizedAffineFiber_coordinate (a : k) (i : Fin q) :
    DiagonalFiniteFundamentalEvaluation.schemeCoordinateUnit
        (normalizedAffineFiberInclusion Z a) i =
      Units.map (AffineEndpointResidueScalar.restrictScalar k
        (FiniteCurveNormalization.ring (coordinateRing Z)) a).toMonoidHom
        (Units.map (algebraMap (coordinateRing Z)
          (FiniteCurveNormalization.ring (coordinateRing Z))).toMonoidHom
            (coordinateUnit Z i)) := by
  apply Units.ext
  have hs := normalizedAffineFiberIso_support Z a
  have h := congrArg Scheme.Hom.appTop hs
  have hv := ConcreteCategory.congr_hom h
    ((Scheme.ΓSpecIso (coordinateRing Z)).inv (coordinateUnit Z i).val)
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at hv
  have hleft : Z.scheme.isoSpec.hom.appTop
      ((Scheme.ΓSpecIso (coordinateRing Z)).inv (coordinateUnit Z i).val) =
        (coordinateUnit Z i).val := by
    change Z.scheme.toSpecΓ.appTop _ = _
    rw [Scheme.toSpecΓ_appTop]
    simp
  rw [hleft] at hv
  have hn := (ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (algebraMap (coordinateRing Z)
        (FiniteCurveNormalization.ring (coordinateRing Z))))) (coordinateUnit Z i).val).symm
  simp only [CommRingCat.comp_apply] at hn
  change (FiniteCurveNormalization.normalizationMap (coordinateRing Z)).appTop
    ((Scheme.ΓSpecIso (coordinateRing Z)).inv (coordinateUnit Z i).val) = _ at hn
  have hv' := hv.trans (congrArg
    (AlgebraicGeometry.FiniteFlatCurve.fiberInclusion
      (AlgebraicGeometry.FiniteAffineEndpointBranches.baseMap
        (FiniteCurveNormalization.ring (coordinateRing Z))) a).appTop hn)
  change ((normalizedAffineFiberInclusion Z a ≫
    DiagonalFinitePointEvaluation.ambientCoordinate k q i).appTop
      (Scheme.PolynomialLaurent.laurentGlobalUnit (.of k)).val) = _
  simp only [normalizedAffineFiberInclusion, normalizedFiberInclusion, Category.assoc,
    Scheme.Hom.comp_appTop]
  have hc := congrArg Units.val (schemeCoordinateUnit_fiberInclusion Z a i)
  change (fiberInclusion Z a ≫ DiagonalFinitePointEvaluation.ambientCoordinate k q i).appTop
    (Scheme.PolynomialLaurent.laurentGlobalUnit (.of k)).val = _ at hc
  exact (congrArg (fun t => (normalizedAffineFiberIso Z a).hom.appTop
    ((normalizedFiberMap Z a).appTop t)) hc).trans hv'

attribute [-instance] DiagonalPointNorm.coordinateField in
/-- The actual original graph endpoint evaluates to its complete normalization sum. -/
theorem cycleValue_endpoint_normalized (a : k) :
    DiagonalPointNorm.cycleValue k q
      ((Cor.graphFunctor k).map (WeightOneBoundaryNorm.evaluationPoint k a) ≫
        (show Cor.mk (AlgebraicSimplex.smoothSiteObj k 1) ⟶
          DiagonalCycleSymbols.target k q from Z.cycle)) = normalizedEndpointValue Z a := by
  let B := coordinateRing Z
  let S := FiniteCurveNormalization.ring B
  let := FiniteCurveNormalization.ring_isDedekindDomain (k := k) B
  let := FiniteCurveNormalization.ring_finite_base (k := k) B
  let := FiniteCurveNormalization.normalizationTorsionFree k B
  let := FiniteCurveNormalization.rationalAlgebra k B
  let : Algebra k S := ((algebraMap k[X] S).comp (algebraMap k k[X])).toAlgebra
  let : IsScalarTower k k[X] S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have h := AffineEndpointGeometricNorm.cycleValue_eq_geometricEndpointValue k S a q
    (fun i => Units.map (algebraMap B S).toMonoidHom (coordinateUnit Z i))
    (normalizedAffineFiberInclusion Z a) (normalizedAffineFiberInclusion_fst Z a)
    (normalizedAffineFiber_coordinate Z a)
    ((Cor.graphFunctor k).map (WeightOneBoundaryNorm.evaluationPoint k a) ≫
      (show Cor.mk (AlgebraicSimplex.smoothSiteObj k 1) ⟶
        DiagonalCycleSymbols.target k q from Z.cycle))
    (toIntegralCycle_endpoint_normalizedAffine Z a)
  exact h.trans (AffineEndpointGeometricNorm.geometricEndpointValue_eq k S (FractionRing B)
    a q _)

attribute [-instance] DiagonalPointNorm.coordinateField in
/-- The full normalized sums agree in every weight, including weight zero. -/
theorem normalizedEndpointValue_eq_all (a b : k) :
    normalizedEndpointValue Z a = normalizedEndpointValue Z b := by
  let B := coordinateRing Z
  let := FiniteCurveNormalization.ring_isDedekindDomain (k := k) B
  let := FiniteCurveNormalization.ring_finite_base (k := k) B
  let := FiniteCurveNormalization.normalizationTorsionFree k B
  let := FiniteCurveNormalization.rationalAlgebra k B
  exact MilnorK.DedekindResidue.endpointWeightedResidueSum_eq_all k
    (FiniteCurveNormalization.ring B) (FractionRing B) a b q _

/-- Every original integral singular support has equal actual endpoint norms. -/
theorem cycleValue_endpoint_generator_eq (a b : k) :
    DiagonalPointNorm.cycleValue k q
      ((Cor.graphFunctor k).map (WeightOneBoundaryNorm.evaluationPoint k a) ≫
        (show Cor.mk (AlgebraicSimplex.smoothSiteObj k 1) ⟶
          DiagonalCycleSymbols.target k q from Z.cycle)) =
    DiagonalPointNorm.cycleValue k q
      ((Cor.graphFunctor k).map (WeightOneBoundaryNorm.evaluationPoint k b) ≫
        (show Cor.mk (AlgebraicSimplex.smoothSiteObj k 1) ⟶
          DiagonalCycleSymbols.target k q from Z.cycle)) := by
  rw [cycleValue_endpoint_normalized, cycleValue_endpoint_normalized,
    normalizedEndpointValue_eq_all Z a b]

end Motivic.DiagonalBoundarySupport
