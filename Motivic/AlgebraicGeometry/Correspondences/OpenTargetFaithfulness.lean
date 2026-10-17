/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.AlgebraicGeometry.Correspondences.FiniteFlatSpanGraph
/-! # Faithful graph postcomposition into an actual open target -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Motivic.Cor
variable {k : Type u} [Field k]

instance graphTargetMap_open (X : SmoothSite (Spec (.of k)))
    {Y Z : SmoothSite (Spec (.of k))} (j : Y ⟶ Z) [IsOpenImmersion j.left] :
    IsOpenImmersion (graphTargetMap k X j) := by
  dsimp [graphTargetMap]
  infer_instance

/-- No signed support or residue multiplicity is lost upon inclusion into an open target. -/
theorem comp_open_graph_injective {X Y Z : SmoothSite (Spec (.of k))}
    (j : Y ⟶ Z) [IsOpenImmersion j.left] :
    Function.Injective (fun a : Cor.mk X ⟶ Cor.mk Y ↦ a ≫ (graphFunctor k).map j) := by
  intro a b h
  apply FiniteCorrespondence.toIntegralCycle_injective
  apply IntegralCycle.toPoints_injective
  have hh := congrArg (fun c ↦ IntegralCycle.toPoints
    (FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := Z.hom) c)) h
  rw [toPoints_comp_graph, toPoints_comp_graph,
    residuePushforward_eq_mapDomain_of_surjectiveOnStalks] at hh
  exact Finsupp.mapDomain_injective (graphTargetMap k X j).isOpenEmbedding.injective hh

end Motivic.Cor
