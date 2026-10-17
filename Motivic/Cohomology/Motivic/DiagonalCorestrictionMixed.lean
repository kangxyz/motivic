/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.DiagonalMixedPointNorm
public import Motivic.Cohomology.Motivic.DiagonalCorestriction

/-!
# All-weight mixed finite transfers

The literal finite point with one varying extension-field coordinate factors
through the original unit point followed by a fixed-coordinate closed immersion.
Its whole pushforward cycle, including residue degrees, satisfies the genuine
norm formula by the full polynomial interpolation in `DiagonalMixedPointNorm`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.DiagonalCorestrictionMixed

open DiagonalCycleSymbols DiagonalCorestriction WeightOneBoundaryNorm

variable {k E : Type u} [Field k] [Field E] [Algebra k E]

/-- Keeping the varying coordinate is a retraction of the literal insertion. -/
instance varyingCoordinate_closed (q : ℕ) (a : Fin q → kˣ) (i : Fin q) :
    IsClosedImmersion (varyingCoordinate k q a i).left := by
  let d := (SmoothSite.torusCoordinate (.of k) q i).left
  have : IsSeparated (d ≫ (SmoothSite.torus (.of k)).hom) := by
    rw [MorphismProperty.Over.w]
    infer_instance
  have : IsSeparated d := IsSeparated.of_comp _ (SmoothSite.torus (.of k)).hom
  have h : (varyingCoordinate k q a i).left ≫ d =
      (SmoothSite.torusPowerOneIso (.of k)).hom.left := by
    have h := congrArg (fun f => f.left)
      (SmoothSite.torusPowerLift_coordinate (.of k) q
        (fun j => if j = i then SmoothSite.torusCoordinate (.of k) 1 0 else
          SmoothSite.torusPowerToBase (.of k) 1 ≫ WeightOnePointNorm.rationalTorusPoint k (a j)) i)
    simp only [ite_true] at h
    exact h
  have : IsClosedImmersion ((varyingCoordinate k q a i).left ≫ d) := by
    rw [h]
    infer_instance
  exact IsClosedImmersion.of_comp _ d

/-- Original mixed tuples, with all unchanged coordinates from the base field. -/
def mixedTuple (q : ℕ) (a : Fin q → kˣ) (i : Fin q) (b : Eˣ) : Fin q → Eˣ :=
  Function.update (fun j => Units.map (algebraMap k E).toMonoidHom (a j)) i b

/-- Exact equality of finite-point maps, before any quotient or cycle evaluation. -/
theorem finitePointMap_varying (q : ℕ) (a : Fin q → kˣ) (i : Fin q) (b : Eˣ) :
    finitePointMap (k := k) q (rationalTuple E q (mixedTuple q a i b)) =
      WeightOneFinitePointNorm.unitPoint (k := k) b ≫
        Cor.graphTargetMap k (SmoothSite.base (Spec (.of k)))
          (varyingCoordinate k q a i) := by
  classical
  apply pullback.hom_ext
  · simp only [finitePointMap_fst, Category.assoc, Cor.graphTargetMap_fst,
      WeightOneFinitePointNorm.unitPoint_projection]
  · apply WeightTwoCorestriction.torusPower_scheme_hom_ext q
    · rw [Category.assoc, ← pullback.condition, ← Category.assoc,
        finitePointMap_fst]
      simp only [Category.assoc, Cor.graphTargetMap_snd,
        MorphismProperty.Over.w,
        WeightTwoCorestriction.unitPoint_snd_projection]
      exact Category.comp_id _
    · intro j
      simp only [Category.assoc, finitePointMap_snd_assoc,
        WeightTwoCorestriction.torusMap_coordinate, Cor.graphTargetMap_snd_assoc]
      have ht := congrArg (fun f => f.left)
        (SmoothSite.torusPowerLift_coordinate (.of E) q
          (fun t => WeightOnePointNorm.rationalTorusPoint E (mixedTuple q a i b t)) j)
      have hv := congrArg (fun f => f.left)
        (SmoothSite.torusPowerLift_coordinate (.of k) q
          (fun t => if t = i then SmoothSite.torusCoordinate (.of k) 1 0 else
            SmoothSite.torusPowerToBase (.of k) 1 ≫
              WeightOnePointNorm.rationalTorusPoint k (a t)) j)
      dsimp only [MorphismProperty.Comma.comp_left] at ht hv
      rw [← Category.assoc]
      erw [ht, hv]
      by_cases hji : j = i
      · subst j
        simp only [mixedTuple, Function.update_self, ite_true]
        rw [WeightTwoCorestriction.unitPoint_coordinate]
        exact WeightTwoCorestriction.rationalTorusPoint_scalar (k := k) b
      · simp only [mixedTuple, Function.update_of_ne hji, hji, ite_false,
          MorphismProperty.Comma.comp_left]
        erw [WeightTwoCorestriction.unitPoint_snd_projection_assoc]
        exact WeightTwoFieldChange.rationalTorusPoint_coefficient (algebraMap k E) (a j)

variable [Module.Finite k E]

/-- Full correspondence equality retains the residue degree of the original point. -/
theorem pointPushforward_varying (q : ℕ) (a : Fin q → kˣ) (i : Fin q) (b : Eˣ) :
    pointPushforward (k := k) q ((Cor.graphFunctor E).map
      (rationalTuple E q (mixedTuple q a i b))) =
      WeightOneFinitePointNorm.unitPointCorrespondence (k := k) b ≫
        (Cor.graphFunctor k).map (varyingCoordinate k q a i) := by
  apply FiniteCorrespondence.toIntegralCycle_injective
  rw [toIntegralCycle_pointPushforward_graph,
    IntegralCycle.finitePushforward_congr (finitePointMap_varying q a i b),
    Cor.toIntegralCycle_comp_graph_of_finite,
    WeightOneFinitePointNorm.toIntegralCycle_unitPointCorrespondence,
    IntegralCycle.finitePushforward_comp]
  rfl

/-- Genuine all-weight corestriction satisfies the arbitrary-position mixed norm formula. -/
theorem corestriction_graphSymbol_varying (q : ℕ) (a : Fin q → kˣ) (i : Fin q) (b : Eˣ) :
    corestriction (k := k) q (graphSymbol E q (mixedTuple q a i b)) =
      graphSymbol k q (Function.update a i (Units.map (Algebra.norm k) b)) := by
  rw [corestriction_graphSymbol, pointPushforward_varying,
    DiagonalMixedPointNorm.finite_point_varying]

end Motivic.DiagonalCorestrictionMixed
