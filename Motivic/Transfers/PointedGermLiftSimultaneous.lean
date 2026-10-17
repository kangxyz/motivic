/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.PointedGermLiftEvaluation

/-! # Simultaneous actual representatives and additive finite lift witnesses -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u v
namespace Motivic.SmoothSite
variable {S : Scheme.{u}} [IsAffine S] {Y : SmoothSite S}
  (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v})

/-- Two original germ classes admit representatives on one actual pointed neighborhood. -/
theorem exists_simultaneous_original_germ_representatives (y : Y.left)
    (a b : (nisnevichPointFiberCocone Y y F).pt) :
    ∃ (R : NisnevichNeighborhood Y y)
      (s t : F.obj (op ((nisnevichNeighborhoodFunctor Y y).obj R))),
      (nisnevichPointFiberCocone Y y F).ι.app (op R) s = a ∧
      (nisnevichPointFiberCocone Y y F).ι.app (op R) t = b := by
  obtain ⟨N, s, hs⟩ := exists_original_germ_representative F y a
  obtain ⟨M, t, ht⟩ := exists_original_germ_representative F y b
  let R := NisnevichNeighborhood.common N M
  let f := NisnevichNeighborhood.commonFst N M
  let g := NisnevichNeighborhood.commonSnd N M
  refine ⟨R, F.map ((nisnevichNeighborhoodFunctor Y y).map f).op s,
    F.map ((nisnevichNeighborhoodFunctor Y y).map g).op t, ?_, ?_⟩
  · have h := (nisnevichPointFiberCocone Y y F).w f.op
    change F.map ((nisnevichNeighborhoodFunctor Y y).map f).op ≫
      (nisnevichPointFiberCocone Y y F).ι.app (op R) =
        (nisnevichPointFiberCocone Y y F).ι.app (op N) at h
    exact (ConcreteCategory.congr_hom h s).trans hs
  · have h := (nisnevichPointFiberCocone Y y F).w g.op
    change F.map ((nisnevichNeighborhoodFunctor Y y).map g).op ≫
      (nisnevichPointFiberCocone Y y F).ι.app (op R) =
        (nisnevichPointFiberCocone Y y F).ι.app (op M) at h
    exact (ConcreteCategory.congr_hom h t).trans ht

end Motivic.SmoothSite
namespace Motivic.PresheafWithTransfers
variable (k : Type u) [Field k] (P : PresheafWithTransfers.{u + 1} k)
  {X Y : SmoothSite (Spec (.of k))}
set_option quotPrecheck false in
local notation "F" => ((toPresheaf k).obj P)

/-- One actual geometric lift simultaneously evaluates two tuples and their sum. -/
theorem exists_additive_pointedGermLiftWitnesses
    (A : FiniteCorrespondenceGenerator X.hom Y.hom) (x : X.left)
    (a b : ∀ y : Y.left, (SmoothSite.nisnevichPointFiberCocone Y y F).pt) :
    ∃ (L : PointedGermLiftWitness k P (show Cor.mk X ⟶ Cor.mk Y from A.cycle) x a)
      (M : PointedGermLiftWitness k P (show Cor.mk X ⟶ Cor.mk Y from A.cycle) x b)
      (N : PointedGermLiftWitness k P (show Cor.mk X ⟶ Cor.mk Y from A.cycle) x (a + b)),
      N.value k P = L.value k P + M.value k P := by
  classical
  choose R s t hs ht using fun y =>
    SmoothSite.exists_simultaneous_original_germ_representatives.{u, 0} F y (a y) (b y)
  let V := fun y => (SmoothSite.nisnevichNeighborhoodFunctor Y y).obj (R y)
  let q : ∀ y, V y ⟶ Y := fun y => (R y).toBase
  have : ∀ y, Etale (q y).left := by intro y; dsimp only [q]; infer_instance
  obtain ⟨U, n, label, β, hβ, hc⟩ :=
    A.exists_pointed_graph_family_factorization_at_chosen_points k x V q
      (fun y => (R y).center) (by
        intro z _
        exact ⟨A.targetProjection z, (R (A.targetProjection z)).toBase_center, inferInstance⟩)
  let L : PointedGermLiftWitness k P (show Cor.mk X ⟶ Cor.mk Y from A.cycle) x a :=
    { source := U, size := n, point := label, target := fun i => R (label i)
      branch := β, graph_eq := hβ, center_control := fun i B hB => (hc i B hB).2
      representative := fun i => s (label i), represents := fun i => hs (label i) }
  let M : PointedGermLiftWitness k P (show Cor.mk X ⟶ Cor.mk Y from A.cycle) x b :=
    { source := U, size := n, point := label, target := fun i => R (label i)
      branch := β, graph_eq := hβ, center_control := fun i B hB => (hc i B hB).2
      representative := fun i => t (label i), represents := fun i => ht (label i) }
  let N : PointedGermLiftWitness k P (show Cor.mk X ⟶ Cor.mk Y from A.cycle) x (a + b) :=
    { source := U, size := n, point := label, target := fun i => R (label i)
      branch := β, graph_eq := hβ, center_control := fun i B hB => (hc i B hB).2
      representative := fun i => s (label i) + t (label i)
      represents := fun i => by simp only [map_add, hs, ht, Pi.add_apply] }
  refine ⟨L, M, N, ?_⟩
  simp only [PointedGermLiftWitness.value, L, M, N, map_add, Finset.sum_add_distrib]

end Motivic.PresheafWithTransfers
