/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.Basic
public import Motivic.AlgebraicGeometry.Correspondences.Coproducts.Binary

/-!
# Graph postcomposition of whole finite-flat spans

The actual finite graph-support pushforward is compared in the faithful
point-cycle dictionary. Its ambient point map need not be finite: only the
support maps are used for geometric pushforward. Thus a retained coordinate
can be forgotten without losing component collisions or residue degrees.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.Cor
open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k]

local instance (T : SmoothSite (Spec (.of k))) : IsNoetherian ((𝟭 Scheme).obj T.left) :=
  inferInstanceAs (IsNoetherian T.left)

local instance (T : SmoothSite (Spec (.of k))) : IsReduced ((𝟭 Scheme).obj T.left) :=
  inferInstanceAs (IsReduced T.left)

/-- The actual graph-composition cycle agrees with the auxiliary residue-weighted
point map, even when the ambient target map is not finite. This follows from
finite pushforward on each actual correspondence support. -/
theorem toPoints_comp_graph {X Y Z : SmoothSite (Spec (.of k))}
    (q : Y ⟶ Z) (α : Cor.mk X ⟶ Cor.mk Y) :
    IntegralCycle.toPoints (FiniteCorrespondence.toIntegralCycle
        (f := X.hom) (g := Z.hom) (α ≫ (graphFunctor k).map q)) =
      FiniteSupportCycle.residuePushforward (graphTargetMap k X q)
        (IntegralCycle.toPoints
          (FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := Y.hom) α)) := by
  have heq :
      IntegralCycle.toPoints.comp
        ((FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := Z.hom)).comp
          ((FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Y) (Z := Z)).flip
            ((graphFunctor k).map q))) =
        (FiniteSupportCycle.residuePushforward (graphTargetMap k X q)).comp
          (IntegralCycle.toPoints.comp
            (FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := Y.hom))) := by
    apply Finsupp.addHom_ext
    intro A n
    have : IsNoetherian A.scheme := isNoetherian_of_finiteType A.projection
    have hsingle : Finsupp.single A n = n • A.cycle := by
      simp [FiniteCorrespondenceGenerator.cycle]
    rw [hsingle]
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.flip_apply, map_zsmul]
    congr 1
    change IntegralCycle.toPoints (FiniteCorrespondence.toIntegralCycle
      (FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Y) (Z := Z)
        A.cycle (componentGraphCycleOver q.left (MorphismProperty.Over.w q)))) =
      FiniteSupportCycle.residuePushforward (graphTargetMap k X q)
        (IntegralCycle.toPoints (FiniteCorrespondence.toIntegralCycle A.cycle))
    rw [A.toIntegralCycle_incidenceTorPairing_componentGraph_right k q.left
      (MorphismProperty.Over.w q)]
    rw [IntegralCycle.toPoints_finitePushforward_apply]
    have hmap : A.graphPostcompositionMap q.left (MorphismProperty.Over.w q) =
        A.inclusion ≫ graphTargetMap k X q := by
      apply pullback.hom_ext <;> simp [FiniteCorrespondenceGenerator.projection,
        FiniteCorrespondenceGenerator.targetProjection, correspondenceProjection,
        FiniteCorrespondenceGenerator.inclusion]
    rw [hmap, FiniteSupportCycle.residuePushforward_comp, AddMonoidHom.comp_apply]
    congr 1
    rw [← IntegralCycle.toPoints_finitePushforward_apply]
    have : IsNoetherian (pullback X.hom Y.hom) :=
      isNoetherian_of_finiteType (pullback.fst X.hom Y.hom)
    change IntegralCycle.toPoints (closedFundamentalCycle A.val) = _
    rw [closedFundamentalCycle_of_isIntegral, FiniteCorrespondenceGenerator.cycle,
      FiniteCorrespondence.toIntegralCycle_single]
    rfl
  exact congrArg (fun f => f α) heq

variable {k}

/-- The original two coordinates retain their base equation after any smooth-site
map of targets. No finiteness of that target map is needed. -/
theorem finiteFlatSpan_postcompose_base {X Y Z : SmoothSite (Spec (.of k))}
    {D : Scheme.{u}} (f : D ⟶ X.left) (g : D ⟶ Y.left)
    (h : f ≫ X.hom = g ≫ Y.hom) (q : Y ⟶ Z) :
    f ≫ X.hom = (g ≫ q.left) ≫ Z.hom := by
  rw [Category.assoc, MorphismProperty.Over.w]
  exact h

/-- Postcomposition by an arbitrary actual graph is the direct finite-flat span
with the target map composed. The original source and all its multiplicities
are unchanged, including when different components acquire the same image. -/
theorem ofFiniteFlatSpan_comp_graph {X Y Z : SmoothSite (Spec (.of k))}
    {D : Scheme.{u}} (f : D ⟶ X.left) [IsFinite f] [Flat f]
    (g : D ⟶ Y.left) (h : f ≫ X.hom = g ≫ Y.hom) (q : Y ⟶ Z) :
    ofFiniteFlatSpan (X := X) (Y := Y) f g h ≫ (graphFunctor k).map q =
      ofFiniteFlatSpan (X := X) (Y := Z) f (g ≫ q.left)
        (finiteFlatSpan_postcompose_base f g h q) := by
  have : IsNoetherian D := isNoetherian_of_finiteType f
  have : IsFinite (pullback.lift f g h) :=
    FiniteFlatCorrespondence.isFinite_productMap f _ (pullback.lift_fst _ _ _)
  have : IsFinite (pullback.lift f (g ≫ q.left) (finiteFlatSpan_postcompose_base f g h q)) :=
    FiniteFlatCorrespondence.isFinite_productMap f _ (pullback.lift_fst _ _ _)
  apply FiniteCorrespondence.toIntegralCycle_injective
  apply IntegralCycle.toPoints_injective
  rw [toPoints_comp_graph, toIntegralCycle_ofFiniteFlatSpan,
    toIntegralCycle_ofFiniteFlatSpan, IntegralCycle.toPoints_finitePushforward_apply,
    IntegralCycle.toPoints_finitePushforward_apply]
  rw [← AddMonoidHom.comp_apply, ← FiniteSupportCycle.residuePushforward_comp]
  congr 2
  apply pullback.hom_ext
  · simp only [Category.assoc, graphTargetMap_fst, pullback.lift_fst]
  · simp only [Category.assoc, graphTargetMap_snd, pullback.lift_snd_assoc,
      pullback.lift_snd]

end Motivic.Cor
