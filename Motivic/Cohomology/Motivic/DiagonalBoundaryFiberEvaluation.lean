/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.DiagonalBoundaryFibers
public import Motivic.Cohomology.Motivic.DiagonalResiduePointEvaluation

/-! # Original singular endpoint cycles and their full intrinsic residue sums -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators
universe u
namespace Motivic.DiagonalBoundarySupport
open WeightOneBoundaryNorm (evaluationPoint)
open DiagonalResiduePointEvaluation
variable {k : Type u} [Field k] [CharZero k] {q : ℕ} (Z : Generator k q)

private instance baseIntegral : IsIntegral (SmoothSite.base (Spec (.of k))).left :=
  inferInstanceAs (IsIntegral (Spec (.of k)))

omit [CharZero k] in
attribute [-instance] DiagonalPointNorm.coordinateField in
/-- Every endpoint coordinate is the restriction of the original global support unit. -/
theorem schemeCoordinateUnit_fiberInclusion (a : k) (i : Fin q) :
    DiagonalFiniteFundamentalEvaluation.schemeCoordinateUnit (fiberInclusion Z a) i =
      Units.map (pullback.snd (evaluationPoint k a).left Z.projection).appTop.hom.toMonoidHom
        (coordinateUnit Z i) := by
  apply Units.ext
  change ((fiberInclusion Z a ≫ DiagonalFinitePointEvaluation.ambientCoordinate k q i).appTop
    (Scheme.PolynomialLaurent.laurentGlobalUnit (.of k)).val) = _
  rw [DiagonalFinitePointEvaluation.ambientCoordinate, ← Category.assoc]
  change (((Z.graphPullbackMap (evaluationPoint k a).left
    (MorphismProperty.Over.w (evaluationPoint k a)) ≫ pullback.snd _ _) ≫ _).appTop _) = _
  rw [Z.graphPullbackMap_snd]
  rw [Category.assoc, Scheme.Hom.comp_appTop]
  rfl

/-- Every original endpoint contributes its full scheme-theoretic local length. -/
def endpointResidueValue (a : k) : MilnorK.K k q := by
  let : Fintype (fiber Z a) := finiteSchemeFintype (fiberProjection Z a)
  exact ∑ x : fiber Z a,
    (IntegralCycle.toPoints (fundamentalCycle (fiber Z a)) x) •
      residueValue (fiberProjection Z a)
        (DiagonalFiniteFundamentalEvaluation.schemeCoordinateUnit (fiberInclusion Z a)) x

/-- The actual graph-composed endpoint cycle evaluates to the whole original fiber. -/
theorem cycleValue_endpoint_generator (a : k) :
    DiagonalPointNorm.cycleValue k q
      ((Cor.graphFunctor k).map (evaluationPoint k a) ≫
        (show Cor.mk (AlgebraicSimplex.smoothSiteObj k 1) ⟶
          DiagonalCycleSymbols.target k q from Z.cycle)) = endpointResidueValue Z a := by
  exact cycleValue_eq_residue_sum_of_finite
    (fiberProjection Z a) (fiberInclusion Z a)
    (Z.graphPullbackMap_fst (evaluationPoint k a).left
      (MorphismProperty.Over.w (evaluationPoint k a)))
    ((Cor.graphFunctor k).map (evaluationPoint k a) ≫
      (show Cor.mk (AlgebraicSimplex.smoothSiteObj k 1) ⟶
        DiagonalCycleSymbols.target k q from Z.cycle))
    (Z.toIntegralCycle_graphFunctor_comp k (evaluationPoint k a))

end Motivic.DiagonalBoundarySupport
