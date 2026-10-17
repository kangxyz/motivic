/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.DiagonalBoundaryFibers
public import Motivic.Aglib.AlgebraicGeometry.FiniteAffineEndpointBranches

/-! # Actual normalized endpoint cycle diagrams in every weight -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Polynomial
universe u
namespace Motivic.DiagonalBoundarySupport
variable {k : Type u} [Field k] [CharZero k] {q : ℕ} (Z : Generator k q)

private instance baseIntegral : IsIntegral (SmoothSite.base (Spec (.of k))).left :=
  inferInstanceAs (IsIntegral (Spec (.of k)))

local instance normalizationFinite :
    IsFinite (FiniteCurveNormalization.normalizationMap (coordinateRing Z)) :=
  FiniteCurveNormalization.normalizationMap_isFinite (k := k) (coordinateRing Z)

local instance supportSpecNoetherian : IsNoetherian (Spec (.of (coordinateRing Z))) :=
  isNoetherian_of_finiteType (FiniteCurveNormalization.baseMap (k := k) (coordinateRing Z))

local instance normalizationSpecNoetherian :
    IsNoetherian (Spec (.of (FiniteCurveNormalization.ring (coordinateRing Z)))) :=
  isNoetherian_of_finiteType (FiniteCurveNormalization.normalizationMap (coordinateRing Z))

/-- The whole endpoint fiber of the actual normalization in the original fraction field. -/
abbrev normalizedFiber (a : k) :=
  FiniteFlatCurve.fiber
    (FiniteCurveNormalization.normalizationMap (coordinateRing Z) ≫
      FiniteCurveNormalization.baseMap (k := k) (coordinateRing Z)) a

/-- The original normalization map followed by the literal support fiber chart. -/
def normalizedFiberMap (a : k) : normalizedFiber Z a ⟶ fiber Z a :=
  FiniteFlatCurve.fiberMap
    (FiniteCurveNormalization.baseMap (k := k) (coordinateRing Z)) a
    (FiniteCurveNormalization.normalizationMap (coordinateRing Z)) ≫
      (affineFiberIso Z a).inv

instance normalizedFiberMapFinite (a : k) : IsFinite (normalizedFiberMap Z a) := by
  unfold normalizedFiberMap
  infer_instance

/-- The finite map from every normalized branch to the original torus product. -/
def normalizedFiberInclusion (a : k) := normalizedFiberMap Z a ≫ fiberInclusion Z a

instance normalizedFiberInclusionFinite (a : k) : IsFinite (normalizedFiberInclusion Z a) := by
  unfold normalizedFiberInclusion
  infer_instance

/-- Normalization preserves the original entire endpoint fundamental cycle. -/
theorem normalizedFiberMap_fundamentalCycle (a : k) :
    IntegralCycle.finitePushforward (normalizedFiberMap Z a)
      (fundamentalCycle (normalizedFiber Z a)) = fundamentalCycle (fiber Z a) := by
  unfold normalizedFiberMap
  rw [IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply]
  rw [FiniteCurveNormalization.finitePushforward_fiber]
  exact finitePushforward_fundamentalCycle (affineFiberIso Z a).inv

/-- The actual original graph-composed endpoint cycle is computed on the full
normalization fiber, retaining proper-image degrees and all Cartier lengths. -/
theorem toIntegralCycle_endpoint_normalized (a : k) :
    (((Cor.graphFunctor k).map (WeightOneBoundaryNorm.evaluationPoint k a) ≫
      (show Cor.mk (AlgebraicSimplex.smoothSiteObj k 1) ⟶
        Cor.mk (SmoothSite.torusPower (.of k) q) from Z.cycle))).toIntegralCycle =
      IntegralCycle.finitePushforward (normalizedFiberInclusion Z a)
        (fundamentalCycle (normalizedFiber Z a)) := by
  unfold normalizedFiberInclusion
  rw [IntegralCycle.finitePushforward_comp,
    AddMonoidHom.comp_apply, normalizedFiberMap_fundamentalCycle]
  exact Z.toIntegralCycle_graphFunctor_comp k (WeightOneBoundaryNorm.evaluationPoint k a)

omit [CharZero k] in
/-- The normalization fiber map keeps the literal original support projection. -/
theorem normalizedFiberMap_support (a : k) :
    normalizedFiberMap Z a ≫
      pullback.snd (WeightOneBoundaryNorm.evaluationPoint k a).left Z.projection ≫
        Z.scheme.isoSpec.hom =
      FiniteFlatCurve.fiberInclusion
        (FiniteCurveNormalization.normalizationMap (coordinateRing Z) ≫
          FiniteCurveNormalization.baseMap (k := k) (coordinateRing Z)) a ≫
            FiniteCurveNormalization.normalizationMap (coordinateRing Z) := by
  simp only [normalizedFiberMap, Category.assoc, affineFiberIso_inv_snd]
  exact FiniteFlatCurve.fiberMap_inclusion _ _ _

/-- The direct polynomial-base fiber and the compositional normalization fiber
are canonically identical over both original projections. -/
def normalizedAffineFiberIso (a : k) :
    FiniteFlatCurve.fiber
      (FiniteAffineEndpointBranches.baseMap (FiniteCurveNormalization.ring (coordinateRing Z))) a ≅
        normalizedFiber Z a :=
  pullback.congrHom rfl
    (FiniteCurveNormalization.normalizationMap_baseMap (k := k) (coordinateRing Z)).symm

/-- The normalized endpoint map in the literal affine base chart. -/
def normalizedAffineFiberInclusion (a : k) :=
  (normalizedAffineFiberIso Z a).hom ≫ normalizedFiberInclusion Z a

instance normalizedAffineFiberInclusionFinite (a : k) :
    IsFinite (normalizedAffineFiberInclusion Z a) := by
  unfold normalizedAffineFiberInclusion
  infer_instance

/-- The graph-composed original endpoint is the full normalized affine-fiber cycle. -/
theorem toIntegralCycle_endpoint_normalizedAffine (a : k) :
    (((Cor.graphFunctor k).map (WeightOneBoundaryNorm.evaluationPoint k a) ≫
      (show Cor.mk (AlgebraicSimplex.smoothSiteObj k 1) ⟶
        Cor.mk (SmoothSite.torusPower (.of k) q) from Z.cycle))).toIntegralCycle =
      IntegralCycle.finitePushforward (normalizedAffineFiberInclusion Z a)
        (fundamentalCycle (FiniteFlatCurve.fiber
          (FiniteAffineEndpointBranches.baseMap
            (FiniteCurveNormalization.ring (coordinateRing Z))) a)) := by
  unfold normalizedAffineFiberInclusion
  rw [IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply,
    finitePushforward_fundamentalCycle]
  exact toIntegralCycle_endpoint_normalized Z a

omit [CharZero k] in
/-- The direct normalization chart retains the original support coordinates. -/
theorem normalizedAffineFiberIso_support (a : k) :
    (normalizedAffineFiberIso Z a).hom ≫ normalizedFiberMap Z a ≫
      pullback.snd (WeightOneBoundaryNorm.evaluationPoint k a).left Z.projection ≫
        Z.scheme.isoSpec.hom =
      FiniteFlatCurve.fiberInclusion
        (FiniteAffineEndpointBranches.baseMap
          (FiniteCurveNormalization.ring (coordinateRing Z))) a ≫
            FiniteCurveNormalization.normalizationMap (coordinateRing Z) := by
  rw [normalizedFiberMap_support]
  simp [normalizedAffineFiberIso, FiniteFlatCurve.fiberInclusion,
    pullback.congrHom_hom, ← Category.assoc]

omit [CharZero k] in
/-- The direct normalization endpoint map is over the original field point. -/
theorem normalizedAffineFiberInclusion_fst (a : k) :
    normalizedAffineFiberInclusion Z a ≫ pullback.fst _ _ =
      pullback.fst (FiniteFlatCurve.endpoint a)
        (FiniteAffineEndpointBranches.baseMap
          (FiniteCurveNormalization.ring (coordinateRing Z))) := by
  simp only [normalizedAffineFiberInclusion, normalizedFiberInclusion,
    Category.assoc, fiberInclusion, FiniteCorrespondenceGenerator.graphPullbackMap_fst]
  simp only [normalizedFiberMap, Category.assoc, affineFiberIso_inv_fst]
  change (normalizedAffineFiberIso Z a).hom ≫
    FiniteFlatCurve.fiberMap
      (FiniteCurveNormalization.baseMap (k := k) (coordinateRing Z)) a
      (FiniteCurveNormalization.normalizationMap (coordinateRing Z)) ≫
    pullback.fst _ _ = _
  simp [normalizedAffineFiberIso, FiniteFlatCurve.fiberMap, pullback.congrHom_hom]

end Motivic.DiagonalBoundarySupport
