/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Sheaf.Germs.Pointed.Lifts.Evaluation
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.FiniteRepresentativeUnion

/-! # Choice independence of actual finite pointed germ-lift evaluations -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u
namespace Motivic.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.SmoothSite.NisnevichNeighborhood
variable (k : Type u) [Field k] (P : PresheafWithTransfers.{u + 1} k)
  (hP : Presheaf.IsSheaf (SmoothSite.nisnevichTopology (Spec (.of k))) ((toPresheaf k).obj P))
  {X Y : SmoothSite (Spec (.of k))}
set_option quotPrecheck false in
local notation "F" => ((toPresheaf k).obj P)
/-- Evaluation using an existing actual finite generator lift; the theorem below
proves this value independent of every such choice for an ordinary Nisnevich sheaf. -/
def generatorGermEvaluation (A : FiniteCorrespondenceGenerator X.hom Y.hom) (x : X.left)
    (a : ∀ y : Y.left, (SmoothSite.nisnevichPointFiberCocone Y y F).pt) :
    (SmoothSite.nisnevichPointFiberCocone X x F).pt :=
  (Classical.choice (exists_pointedGermLiftWitness k P A x a)).value k P

include hP

/-- All actual finite witnesses yield the same element of the original source
point fiber, including different source neighborhoods and different representatives. -/
theorem PointedGermLiftWitness.value_eq {δ : Cor.mk X ⟶ Cor.mk Y} {x : X.left}
    {a : ∀ y : Y.left, (SmoothSite.nisnevichPointFiberCocone Y y F).pt}
    (L M : PointedGermLiftWitness k P δ x a) : L.value k P = M.value k P := by
  let y := appendPoints L.point L.target M.point M.target
  let R := appendFamily L.point L.target M.point M.target
  let e := appendLeftIso L.point L.target M.point M.target
  let e' := appendRightIso L.point L.target M.point M.target
  let β := fun i => L.branch i ≫ (Cor.graphFunctor k).map (e i).hom
  let β' := fun j => M.branch j ≫ (Cor.graphFunctor k).map (e' j).hom
  have hβ : (∑ i, β i ≫ (Cor.graphFunctor k).map (R (Fin.castAdd M.size i)).toBase) =
      (Cor.graphFunctor k).map L.source.toBase ≫ δ := by
    simpa only [β, e, R, Category.assoc, ← Functor.map_comp, appendLeftIso_hom_toBase]
      using L.graph_eq
  have hβ' : (∑ j, β' j ≫ (Cor.graphFunctor k).map (R (Fin.natAdd L.size j)).toBase) =
      (Cor.graphFunctor k).map M.source.toBase ≫ δ := by
    simpa only [β', e', R, Category.assoc, ← Functor.map_comp, appendRightIso_hom_toBase]
      using M.graph_eq
  have hc : ∀ i A, A ∈ (β i).support → ∀ z : A.scheme,
      A.projection z = L.source.center →
        A.targetProjection z = (R (Fin.castAdd M.size i)).center := by
    intro i A hA z hz
    obtain ⟨B, hB, b, hs, ht⟩ :=
      FiniteCorrespondence.exists_support_point_lift_of_mem_comp_graph
        (L.branch i) (e i).hom A hA z
    rw [L.center_control i B hB b (hs.trans hz)] at ht
    exact ht.symm.trans (appendLeftIso_hom_center L.point L.target M.point M.target i)
  have hc' : ∀ j A, A ∈ (β' j).support → ∀ z : A.scheme,
      A.projection z = M.source.center →
        A.targetProjection z = (R (Fin.natAdd L.size j)).center := by
    intro j A hA z hz
    obtain ⟨B, hB, b, hs, ht⟩ :=
      FiniteCorrespondence.exists_support_point_lift_of_mem_comp_graph
        (M.branch j) (e' j).hom A hA z
    rw [M.center_control j B hB b (hs.trans hz)] at ht
    exact ht.symm.trans (appendRightIso_hom_center L.point L.target M.point M.target j)
  let s := appendSections.{u, 0} L.point L.target M.point M.target F
    L.representative M.representative
  have hs := appendSections_represents.{u, 0} L.point L.target M.point M.target F
    L.representative M.representative a L.represents M.represents
  have h := family_transfer_cocone_eq k P hP y R x L.source M.source δ
    (Fin.castAdd M.size) (Fin.natAdd L.size) β β' hβ hβ' hc hc' a s hs
  have heval : ∀ i, P.transfer (β i) (s (Fin.castAdd M.size i)) =
      P.transfer (L.branch i) (L.representative i) := by
    intro i
    dsimp only [β]
    rw [transfer_comp]
    change P.transfer (L.branch i) ((F).map (e i).hom.op
      (s (Fin.castAdd M.size i))) = _
    rw [appendSections_left.{u, 0}]
  have heval' : ∀ j, P.transfer (β' j) (s (Fin.natAdd L.size j)) =
      P.transfer (M.branch j) (M.representative j) := by
    intro j
    dsimp only [β']
    rw [transfer_comp]
    change P.transfer (M.branch j) ((F).map (e' j).hom.op
      (s (Fin.natAdd L.size j))) = _
    rw [appendSections_right.{u, 0}]
  have hsum : (∑ i, P.transfer (β i) (s (Fin.castAdd M.size i))) =
      ∑ i, P.transfer (L.branch i) (L.representative i) :=
    Finset.sum_congr rfl (fun i _ => heval i)
  have hsum' : (∑ j, P.transfer (β' j) (s (Fin.natAdd L.size j))) =
      ∑ j, P.transfer (M.branch j) (M.representative j) :=
    Finset.sum_congr rfl (fun j _ => heval' j)
  have hL := congrArg (fun z =>
    (SmoothSite.nisnevichPointFiberCocone X x F).ι.app (op L.source) z) hsum
  have hM := congrArg (fun z =>
    (SmoothSite.nisnevichPointFiberCocone X x F).ι.app (op M.source) z) hsum'
  exact hL.symm.trans (h.trans hM)

/-- The chosen evaluation equals the value of any actual original finite witness. -/
theorem generatorGermEvaluation_eq_of_witness
    (A : FiniteCorrespondenceGenerator X.hom Y.hom) (x : X.left)
    (a : ∀ y : Y.left, (SmoothSite.nisnevichPointFiberCocone Y y F).pt)
    (L : PointedGermLiftWitness k P (show Cor.mk X ⟶ Cor.mk Y from A.cycle) x a) :
    generatorGermEvaluation k P A x a = L.value k P :=
  PointedGermLiftWitness.value_eq k P hP _ L

end Motivic.PresheafWithTransfers
