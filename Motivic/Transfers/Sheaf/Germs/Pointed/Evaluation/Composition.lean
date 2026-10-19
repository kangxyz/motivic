/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Sheaf.Germs.Pointed.Evaluation.Witness
public import Motivic.Transfers.Sheaf.Germs.Pointed.Lifts.Composition
public import Motivic.Transfers.PointedGermLiftGraph

/-! # Actual signed composition and graph laws on original germ tuples -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Opposite AlgebraicGeometry
universe u
namespace Motivic.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme
variable (k : Type u) [Field k] (P : PresheafWithTransfers.{u + 1} k)
  (hP : Presheaf.IsSheaf (SmoothSite.nisnevichTopology (Spec (.of k))) ((toPresheaf k).obj P))
  {X Y Z : SmoothSite (Spec (.of k))}
set_option quotPrecheck false in
local notation "F" => ((toPresheaf k).obj P)

/-- Composition with a generator is computed on genuinely nested finite lifts. -/
theorem correspondenceGermHom_cycle_comp
    (A : FiniteCorrespondenceGenerator X.hom Y.hom) (β : Cor.mk Y ⟶ Cor.mk Z)
    (x : X.left)
    (a : ∀ z : Z.left, (SmoothSite.nisnevichPointFiberCocone Z z F).pt) :
    correspondenceGermHom k P hP x
        ((show Cor.mk X ⟶ Cor.mk Y from A.cycle) ≫ β) a =
      generatorGermEvaluation k P A x (fun y => correspondenceGermHom k P hP y β a) := by
  classical
  choose L hL using fun y => exists_signed_pointedGermLiftWitness k P hP β y a
  obtain ⟨M, N, h⟩ := exists_composed_generator_germ_witnesses k P A β x a L
  rw [correspondenceGermHom_eq_of_witness k P hP _ x a N, h,
    ← generatorGermEvaluation_eq_of_witness k P hP A x _ M]
  exact congrArg (generatorGermEvaluation k P A x) (funext hL)

/-- The original signed finite-correspondence composition acts contravariantly
on tuples of the original Nisnevich point fibers. -/
theorem correspondenceGermHom_comp
    (α : Cor.mk X ⟶ Cor.mk Y) (β : Cor.mk Y ⟶ Cor.mk Z) (x : X.left)
    (a : ∀ z : Z.left, (SmoothSite.nisnevichPointFiberCocone Z z F).pt) :
    correspondenceGermHom k P hP x (α ≫ β) a =
      correspondenceGermHom k P hP x α (fun y => correspondenceGermHom k P hP y β a) := by
  classical
  induction α using Finsupp.induction_linear with
  | zero =>
    have hz : (0 : Cor.mk X ⟶ Cor.mk Y) ≫ β = 0 :=
      (FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Y) (Z := Z)).flip β |>.map_zero
    rw [hz, map_zero, AddMonoidHom.zero_apply, map_zero, AddMonoidHom.zero_apply]
  | add γ η hγ hη =>
    have hadd : (show Cor.mk X ⟶ Cor.mk Y from γ + η) ≫ β = γ ≫ β + η ≫ β :=
      (FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Y) (Z := Z)).flip β |>.map_add γ η
    rw [hadd]
    simp only [map_add, AddMonoidHom.add_apply, hγ, hη]
  | single A m =>
    have hm : Finsupp.single A m = m • A.cycle := by
      simp [FiniteCorrespondenceGenerator.cycle, Finsupp.smul_single]
    rw [hm, Preadditive.zsmul_comp]
    simp only [map_zsmul, AddMonoidHom.zsmul_apply, correspondenceGermHom_cycle,
      correspondenceGermHom_cycle_comp]
    rfl

/-- On a graph the signed action is the literal pullback of the original germ
at the image point, constructed from the original point-fiber colimit. -/
theorem correspondenceGermHom_graph (f : X ⟶ Y) (x : X.left)
    (a : ∀ y : Y.left, (SmoothSite.nisnevichPointFiberCocone Y y F).pt) :
    correspondenceGermHom k P hP x ((Cor.graphFunctor k).map f) a =
      SmoothSite.originalGermPullback.{u, 0} F f x (a (f.left x)) := by
  obtain ⟨L⟩ := exists_pointedGermLiftWitness_graph k P f x a
  rw [correspondenceGermHom_eq_of_witness k P hP _ x a L]
  exact PointedGermLiftWitness.value_graph k P hP f x a L

/-- The original identity correspondence acts as evaluation at the same point. -/
theorem correspondenceGermHom_id (x : X.left)
    (a : ∀ y : X.left, (SmoothSite.nisnevichPointFiberCocone X y F).pt) :
    correspondenceGermHom k P hP x (𝟙 (Cor.mk X)) a = a x := by
  obtain ⟨N, s, hs⟩ := SmoothSite.exists_original_germ_representative.{u, 0} F x (a x)
  let V := (SmoothSite.nisnevichNeighborhoodFunctor X x).obj N
  have hid : (Cor.graphFunctor k).map (𝟙 V) = 𝟙 (Cor.mk V) :=
    (Cor.graphFunctor k).map_id V
  let L : PointedGermLiftWitness k P (𝟙 (Cor.mk X)) x a :=
    { source := N, size := 1, point := fun _ => x, target := fun _ => N
      branch := fun _ => (Cor.graphFunctor k).map (𝟙 V)
      graph_eq := by
        rw [Fin.sum_univ_one, hid]
        exact (Category.id_comp ((Cor.graphFunctor k).map N.toBase)).trans
          (Category.comp_id ((Cor.graphFunctor k).map N.toBase)).symm
      center_control := fun _ A hA z hz => by
        have h := congrArg (fun f => f z) (A.projection_target_of_mem_graph (𝟙 V) hA)
        change A.projection z = A.targetProjection z at h
        exact h.symm.trans hz
      representative := fun _ => s, represents := fun _ => hs }
  rw [correspondenceGermHom_eq_of_witness k P hP _ x a L]
  change (SmoothSite.nisnevichPointFiberCocone X x F).ι.app (op N)
    (∑ _ : Fin 1, P.transfer ((Cor.graphFunctor k).map (𝟙 V)) s) = a x
  rw [Fin.sum_univ_one, (Cor.graphFunctor k).map_id V, transfer_id]
  exact hs

end Motivic.PresheafWithTransfers
