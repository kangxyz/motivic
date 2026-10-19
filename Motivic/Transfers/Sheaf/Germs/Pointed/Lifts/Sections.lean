/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Sheaf.Germs.Pointed.Lifts.Evaluation

/-! # Finite germ-lift evaluation on actual global sections -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u
namespace Motivic.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme
variable (k : Type u) [Field k] (P : PresheafWithTransfers.{u + 1} k)
  {X Y : SmoothSite (Spec (.of k))}
set_option quotPrecheck false in
local notation "F" => ((toPresheaf k).obj P)

/-- A finite actual lift evaluated on restrictions of one section is the
original transfer followed by the original source germ map. -/
theorem PointedGermLiftWitness.value_eq_transfer_of_restrictions
    {δ : Cor.mk X ⟶ Cor.mk Y} {x : X.left}
    {a : ∀ y : Y.left, (SmoothSite.nisnevichPointFiberCocone Y y F).pt}
    (L : PointedGermLiftWitness k P δ x a) (s : P.sections (Cor.mk Y))
    (hs : ∀ i, L.representative i = (F).map (L.target i).toBase.op s) :
    L.value k P = SmoothSite.sectionToNisnevichPoint.{u, 0} F X x (P.transfer δ s) := by
  let U := (SmoothSite.nisnevichNeighborhoodFunctor X x).obj L.source
  let e : (Cor.mk U ⟶ Cor.mk Y) →+ P.sections (Cor.mk U) :=
    { toFun := fun γ => P.transfer γ s
      map_zero' := by simp
      map_add' := fun γ η => by simp only [transfer_add, AddCommGrpCat.hom_add_apply] }
  have he : (∑ i, P.transfer (L.branch i) (L.representative i)) =
      (F).map L.source.toBase.op (P.transfer δ s) := by
    have h := congrArg (fun γ => e γ) L.graph_eq
    rw [map_sum] at h
    have hterm : ∀ i, e (L.branch i ≫ (Cor.graphFunctor k).map (L.target i).toBase) =
        P.transfer (L.branch i) (L.representative i) := by
      intro i
      dsimp only [e, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [transfer_comp, hs i]
      rfl
    rw [Finset.sum_congr rfl (fun i _ => hterm i)] at h
    change _ = P.transfer ((Cor.graphFunctor k).map L.source.toBase ≫ δ) s at h
    rw [transfer_comp] at h
    exact h
  dsimp only [PointedGermLiftWitness.value]
  rw [he]
  exact ConcreteCategory.congr_hom
    (SmoothSite.restriction_sectionToNisnevichPoint.{u, 0} F L.source) (P.transfer δ s)

end Motivic.PresheafWithTransfers
