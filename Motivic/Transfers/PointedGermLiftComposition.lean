/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.PointedGermLiftEvaluation
public import Motivic.AlgebraicGeometry.Correspondences.CompositionPointControl

/-! # Nested actual finite germ witnesses for correspondence composition -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u
namespace Motivic.PresheafWithTransfers
variable (k : Type u) [Field k] (P : PresheafWithTransfers.{u + 1} k)
  {X Y Z : SmoothSite (Spec (.of k))}
set_option quotPrecheck false in
local notation "F" => ((toPresheaf k).obj P)

/-- Choose actual inner witnesses at every intermediate point. The original
geometric generator lift then produces compatible outer and composite witnesses;
their values agree by the original presheaf transfer composition. -/
theorem exists_composed_generator_germ_witnesses
    (A : FiniteCorrespondenceGenerator X.hom Y.hom) (β : Cor.mk Y ⟶ Cor.mk Z)
    (x : X.left)
    (a : ∀ z : Z.left, (SmoothSite.nisnevichPointFiberCocone Z z F).pt)
    (L : ∀ y : Y.left, PointedGermLiftWitness k P β y a) :
    ∃ (M : PointedGermLiftWitness k P (show Cor.mk X ⟶ Cor.mk Y from A.cycle) x
        (fun y => (L y).value k P))
      (N : PointedGermLiftWitness k P
        ((show Cor.mk X ⟶ Cor.mk Y from A.cycle) ≫ β) x a),
      N.value k P = M.value k P := by
  classical
  let V := fun y => (SmoothSite.nisnevichNeighborhoodFunctor Y y).obj (L y).source
  let q : ∀ y, V y ⟶ Y := fun y => (L y).source.toBase
  have : ∀ y, Etale (q y).left := by intro y; dsimp only [q]; infer_instance
  obtain ⟨U, n, label, γ, hγ, hc⟩ :=
    A.exists_pointed_graph_family_factorization_at_chosen_points k x V q
      (fun y => (L y).source.center) (by
        intro z _
        exact ⟨A.targetProjection z, (L (A.targetProjection z)).source.toBase_center,
          inferInstance⟩)
  let M : PointedGermLiftWitness k P (show Cor.mk X ⟶ Cor.mk Y from A.cycle) x
      (fun y => (L y).value k P) :=
    { source := U, size := n, point := label, target := fun i => (L (label i)).source
      branch := γ, graph_eq := hγ, center_control := fun i B hB => (hc i B hB).2
      representative := fun i => ∑ j,
        P.transfer ((L (label i)).branch j) ((L (label i)).representative j)
      represents := fun _ => rfl }
  let I := Σ i : Fin n, Fin (L (label i)).size
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let branch := fun t : I => γ t.1 ≫ (L (label t.1)).branch t.2
  have hsum : (∑ t : I, branch t ≫
      (Cor.graphFunctor k).map ((L (label t.1)).target t.2).toBase) =
      (Cor.graphFunctor k).map U.toBase ≫
        ((show Cor.mk X ⟶ Cor.mk Y from A.cycle) ≫ β) := by
    dsimp only [branch]
    rw [Fintype.sum_sigma]
    simp_rw [Category.assoc, ← Preadditive.comp_sum, (L _).graph_eq,
      ← Category.assoc]
    rw [← Preadditive.sum_comp, hγ, Category.assoc]
  let N : PointedGermLiftWitness k P
      ((show Cor.mk X ⟶ Cor.mk Y from A.cycle) ≫ β) x a :=
    { source := U, size := Fintype.card I
      point := fun t => (L (label (e t).1)).point (e t).2
      target := fun t => (L (label (e t).1)).target (e t).2
      branch := fun t => branch (e t)
      graph_eq := (e.sum_comp _).trans hsum
      center_control := fun t B hB b hb =>
        FiniteCorrespondence.target_eq_of_mem_comp (γ (e t).1)
          ((L (label (e t).1)).branch (e t).2) U.center
          (L (label (e t).1)).source.center ((L (label (e t).1)).target (e t).2).center
          (fun C hC => (hc (e t).1 C hC).2)
          ((L (label (e t).1)).center_control (e t).2) B hB b hb
      representative := fun t => (L (label (e t).1)).representative (e t).2
      represents := fun t => (L (label (e t).1)).represents (e t).2 }
  refine ⟨M, N, ?_⟩
  have hv : (∑ t : Fin (Fintype.card I),
      P.transfer (branch (e t)) ((L (label (e t).1)).representative (e t).2)) =
      ∑ i, P.transfer (γ i) (∑ j,
        P.transfer ((L (label i)).branch j) ((L (label i)).representative j)) := by
    refine (e.sum_comp (fun t : I =>
      P.transfer (branch t) ((L (label t.1)).representative t.2))).trans ?_
    rw [Fintype.sum_sigma]
    simp only [branch, transfer_comp, map_sum]
    rfl
  exact congrArg ((SmoothSite.nisnevichPointFiberCocone X x F).ι.app (op U)) hv

end Motivic.PresheafWithTransfers
